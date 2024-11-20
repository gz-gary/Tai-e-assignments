/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New newStmt) {
            VarPtr ptr = pointerFlowGraph.getVarPtr(newStmt.getLValue());
            Obj obj = heapModel.getObj(newStmt);
            PointsToSet objSet = new PointsToSet(obj);
            workList.addEntry(ptr, objSet);
            return null;
        }

        @Override
        public Void visit(Copy copyStmt) {
            VarPtr ptrLeft = pointerFlowGraph.getVarPtr(copyStmt.getLValue());
            VarPtr ptrRight = pointerFlowGraph.getVarPtr(copyStmt.getRValue());
            addPFGEdge(ptrRight, ptrLeft);
            return null;
        }

        @Override
        public Void visit(StoreField storeStmt) {
            JField field = storeStmt.getFieldRef().resolve();
            if (field.isStatic()) {
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr varPtr = pointerFlowGraph.getVarPtr(storeStmt.getRValue());
                addPFGEdge(varPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField loadStmt) {
            JField field = loadStmt.getFieldRef().resolve();
            if (field.isStatic()) {
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                VarPtr varPtr = pointerFlowGraph.getVarPtr(loadStmt.getLValue());
                addPFGEdge(staticField, varPtr);
            }
            return null;
        }

        @Override
        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                JMethod callTarget = resolveCallee(null, invoke);
                Edge<Invoke, JMethod> callEdge = new Edge<>(CallKind.STATIC, invoke, callTarget);
                if (callGraph.addEdge(callEdge)) {
                    addReachable(callTarget);
                    int cntParam = callTarget.getParamCount();
                    assert(cntParam == invoke.getInvokeExp().getArgCount());
                    for (int i = 0; i < cntParam; ++i) {
                        VarPtr varOutside = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                        VarPtr varInside = pointerFlowGraph.getVarPtr(callTarget.getIR().getParam(i));
                        addPFGEdge(varOutside, varInside);
                    }

                    if (invoke.getLValue() != null) {
                        VarPtr resultOutside = pointerFlowGraph.getVarPtr(invoke.getLValue());
                        for (Var returnVar : callTarget.getIR().getReturnVars()) {
                            VarPtr resultInside = pointerFlowGraph.getVarPtr(returnVar);
                            addPFGEdge(resultInside, resultOutside);
                        }
                    }
                }
            }
            return null;
        }
        //  via visitor pattern, then finish me
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // if s -> t already exists
        if (pointerFlowGraph.addEdge(source, target)) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            PointsToSet deltaSet = propagate(pointer, pointsToSet);
            for (Obj obj : deltaSet) pointer.getPointsToSet().addObject(obj);
            if (pointer instanceof VarPtr varPtr) {
                for (Obj obj : deltaSet) {
                    for (StoreField storeStmt : varPtr.getVar().getStoreFields()) {
                        InstanceField field = pointerFlowGraph.getInstanceField(obj, storeStmt.getFieldRef().resolve());
                        VarPtr varStored = pointerFlowGraph.getVarPtr(storeStmt.getRValue());
                        addPFGEdge(varStored, field);
                    }

                    for (LoadField loadStmt : varPtr.getVar().getLoadFields()) {
                        InstanceField field = pointerFlowGraph.getInstanceField(obj, loadStmt.getFieldRef().resolve());
                        VarPtr varLoaded = pointerFlowGraph.getVarPtr(loadStmt.getLValue());
                        addPFGEdge(field, varLoaded);
                    }
                    
                    for (StoreArray storeArray : varPtr.getVar().getStoreArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr varStored = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(varStored, arrayIndex);
                    }

                    for (LoadArray loadArray : varPtr.getVar().getLoadArrays()) {
                        ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr varLoaded = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        addPFGEdge(arrayIndex, varLoaded);
                    }
                    
                    processCall(varPtr.getVar(), obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet deltaSet = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                deltaSet.addObject(obj);
            }
        }
        if (!deltaSet.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, deltaSet);
            }
        }
        return deltaSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            JMethod method = resolveCallee(recv, invoke);
            workList.addEntry(
                pointerFlowGraph.getVarPtr(method.getIR().getThis()),
                new PointsToSet(recv)
            );
            if (callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, invoke, method))) {
                addReachable(method);
                int cntParam = method.getParamCount();
                assert(cntParam == invoke.getInvokeExp().getArgCount());
                for (int i = 0; i < cntParam; ++i) {
                    VarPtr varOutside = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                    VarPtr varInside = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
                    addPFGEdge(varOutside, varInside);
                }

                if (invoke.getLValue() != null) {
                    VarPtr resultOutside = pointerFlowGraph.getVarPtr(invoke.getLValue());
                    for (Var returnVar : method.getIR().getReturnVars()) {
                        VarPtr resultInside = pointerFlowGraph.getVarPtr(returnVar);
                        addPFGEdge(resultInside, resultOutside);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
