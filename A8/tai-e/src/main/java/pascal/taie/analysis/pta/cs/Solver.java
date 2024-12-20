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

package pascal.taie.analysis.pta.cs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeVirtual;
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
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private final Map<Var, Set<Pair<Invoke, Integer>>> varAsArgInvokeSite;

    private Set<Pair<Invoke, Integer>> getVarAsArgInvokeSites(Var x) {
        return varAsArgInvokeSite.getOrDefault(x, new HashSet<>());
    };

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.varAsArgInvokeSite = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    public CSCallGraph getCSCallGraph() {
        return callGraph;
    }

    void solve() {
        initialize();
        analyze();
        /* Do taints transfer when callgraph construction is complete */
        for (CSMethod csMethod : callGraph.getNodes()) {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                if (stmt instanceof Invoke invoke) {
                    if (invoke.isStatic() && invoke.getLValue() != null) {
                        CSVar resultOutside = csManager.getCSVar(csMethod.getContext(), invoke.getLValue());
                        workList.addEntry(
                            resultOutside,
                            taintAnalysis.getTaintObjects(resolveCallee(null, invoke), invoke)
                        );
                    }
                }
            }
        }
        /* analyze again with taint objects */
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        if (callGraph.addReachableMethod(csMethod)) {
            /* record where var is used as arg */
            List<Stmt> stmts = csMethod.getMethod().getIR().getStmts();
            for (Stmt stmt : stmts) {
                if (stmt instanceof Invoke invoke) {
                    InvokeExp invokeExp = invoke.getInvokeExp();
                    for (int i = 0; i < invokeExp.getArgCount(); ++i) {
                        Var arg = invokeExp.getArg(i);
                        Set<Pair<Invoke, Integer>> lst = varAsArgInvokeSite.getOrDefault(arg, new HashSet<>());
                        lst.add(new Pair<>(invoke, i));
                        varAsArgInvokeSite.put(arg, lst);
                    }
                }
            }


            for (Stmt stmt : stmts) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        @Override
        public Void visit(New newStmt) {
            CSVar ptr = csManager.getCSVar(context, newStmt.getLValue());
            Obj obj = heapModel.getObj(newStmt);

            Context objContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(objContext, obj);

            PointsToSet objSet = PointsToSetFactory.make(csObj);
            workList.addEntry(ptr, objSet);
            return null;
        }

        @Override
        public Void visit(Copy copyStmt) {
            CSVar ptrLeft = csManager.getCSVar(context, copyStmt.getLValue());
            CSVar ptrRight = csManager.getCSVar(context, copyStmt.getRValue());
            addPFGEdge(ptrRight, ptrLeft);
            return null;
        }

        @Override
        public Void visit(StoreField storeStmt) {
            JField field = storeStmt.getFieldRef().resolve();
            if (field.isStatic()) {
                StaticField staticField = csManager.getStaticField(field);
                CSVar varPtr = csManager.getCSVar(context, storeStmt.getRValue());
                addPFGEdge(varPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(LoadField loadStmt) {
            JField field = loadStmt.getFieldRef().resolve();
            if (field.isStatic()) {
                StaticField staticField = csManager.getStaticField(field);
                CSVar varPtr = csManager.getCSVar(context, loadStmt.getLValue());
                addPFGEdge(staticField, varPtr);
            }
            return null;
        }

        @Override
        public Void visit(Invoke invoke) {
            if (invoke.isStatic()) {
                JMethod callTarget = resolveCallee(null, invoke);
                CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
                Context targetContext = contextSelector.selectContext(
                    csCallSite,
                    callTarget
                );
                CSMethod csTarget = csManager.getCSMethod(targetContext, callTarget);
                Edge<CSCallSite, CSMethod> callEdge = new Edge<>(
                    CallKind.STATIC,
                    csCallSite,
                    csTarget
                );
                if (callGraph.addEdge(callEdge)) {
                    addReachable(csTarget);
                    int cntParam = callTarget.getParamCount();
                    assert(cntParam == invoke.getInvokeExp().getArgCount());

                    for (int i = 0; i < cntParam; ++i) {
                        CSVar varOutside = csManager.getCSVar(context, invoke.getInvokeExp().getArg(i));
                        CSVar varInside = csManager.getCSVar(targetContext, callTarget.getIR().getParam(i));
                        addPFGEdge(varOutside, varInside);
                    }

                    if (invoke.getLValue() != null) {
                        CSVar resultOutside = csManager.getCSVar(context, invoke.getLValue());
                        callTarget.getIR().getReturnVars();
                        for (Var returnVar : callTarget.getIR().getReturnVars()) {
                            CSVar resultInside = csManager.getCSVar(targetContext, returnVar);
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
            for (CSObj obj : deltaSet) pointer.getPointsToSet().addObject(obj);
            if (pointer instanceof CSVar ptr) {
                Context xContext = ptr.getContext();
                for (CSObj obj : deltaSet) {
                    for (StoreField storeStmt : ptr.getVar().getStoreFields()) {
                        InstanceField field = csManager.getInstanceField(obj, storeStmt.getFieldRef().resolve());
                        CSVar varStored = csManager.getCSVar(xContext, storeStmt.getRValue());
                        addPFGEdge(varStored, field);
                    }

                    for (LoadField loadStmt : ptr.getVar().getLoadFields()) {
                        InstanceField field = csManager.getInstanceField(obj, loadStmt.getFieldRef().resolve());
                        CSVar varLoaded = csManager.getCSVar(xContext, loadStmt.getLValue());
                        addPFGEdge(field, varLoaded);
                    }
                    
                    for (StoreArray storeArray : ptr.getVar().getStoreArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        CSVar varStored = csManager.getCSVar(xContext, storeArray.getRValue());
                        addPFGEdge(varStored, arrayIndex);
                    }

                    for (LoadArray loadArray : ptr.getVar().getLoadArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                        CSVar varLoaded = csManager.getCSVar(xContext, loadArray.getLValue());
                        addPFGEdge(arrayIndex, varLoaded);
                    }
                    
                    processCall(ptr, obj);
                }
                for (CSObj csObj : deltaSet) if (
                    taintAnalysis.isTaint(csObj.getObject())
                    // && csObj.getContext().equals(contextSelector.getEmptyContext())
                ) {
                    /* handle base to result rules */
                    for (Invoke invoke : ptr.getVar().getInvokes()) {
                        if (invoke.getLValue() == null) continue;
                        CSCallSite csCallSite = csManager.getCSCallSite(ptr.getContext(), invoke);
                        for (CSMethod csMethod : callGraph.getCalleesOf(csCallSite)) {
                            JMethod method = csMethod.getMethod();
                            for (Type type : taintAnalysis.getMatchBaseToResultTypes(method)) {
                                CSVar returnVar = csManager.getCSVar(ptr.getContext(), invoke.getLValue());
                                CSObj newTaintObj = csManager.getCSObj(
                                    csObj.getContext(),
                                    taintAnalysis.makeTaint(taintAnalysis.getSourceCall(csObj.getObject()), type)
                                );
                                workList.addEntry(returnVar, PointsToSetFactory.make(newTaintObj));
                            }
                        }
                    }

                    /* handle arg to result rules */
                    for (Pair<Invoke, Integer> pair : getVarAsArgInvokeSites(ptr.getVar())) {
                        Invoke invoke = pair.first();
                        if (invoke.getLValue() == null) continue;
                        int idx = pair.second();
                        CSCallSite csCallSite = csManager.getCSCallSite(ptr.getContext(), invoke);
                        for (CSMethod csMethod : callGraph.getCalleesOf(csCallSite)) {
                            JMethod method = csMethod.getMethod();
                            for (Type type : taintAnalysis.getMatchArgToResultTypes(method, idx)) {
                                CSVar returnVar = csManager.getCSVar(ptr.getContext(), invoke.getLValue());
                                CSObj newTaintObj = csManager.getCSObj(
                                    contextSelector.getEmptyContext(),
                                    taintAnalysis.makeTaint(taintAnalysis.getSourceCall(csObj.getObject()), type)
                                );
                                workList.addEntry(returnVar, PointsToSetFactory.make(newTaintObj));
                            }
                        }
                    }

                    /* handle arg to base rules */
                    for (Pair<Invoke, Integer> pair : getVarAsArgInvokeSites(ptr.getVar())) {
                        Invoke invoke = pair.first();
                        int idx = pair.second();
                        if (invoke.getInvokeExp() instanceof InvokeVirtual invokeVirtual) {
                            Var base = invokeVirtual.getBase();
                            CSVar csBase = csManager.getCSVar(csObj.getContext(), base);
                            CSCallSite csCallSite = csManager.getCSCallSite(ptr.getContext(), invoke);
                            for (CSMethod csMethod : callGraph.getCalleesOf(csCallSite)) {
                                JMethod method = csMethod.getMethod();
                                for (Type type : taintAnalysis.getMatchArgToBaseTypes(method, idx)) {
                                    CSObj newTaintObj = csManager.getCSObj(
                                        contextSelector.getEmptyContext(),
                                        taintAnalysis.makeTaint(taintAnalysis.getSourceCall(csObj.getObject()), type)
                                    );
                                    workList.addEntry(csBase, PointsToSetFactory.make(newTaintObj));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet deltaSet = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke invoke : recv.getVar().getInvokes()) {
            JMethod target = resolveCallee(recvObj, invoke);
            Context recvContext = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(recvContext, invoke);
            Context targetContext = contextSelector.selectContext(csCallSite, recvObj, target);
            CSMethod csTarget = csManager.getCSMethod(targetContext, target);
            workList.addEntry(
                csManager.getCSVar(targetContext, target.getIR().getThis()),
                PointsToSetFactory.make(recvObj)
            );
            if (callGraph.addEdge(new Edge<>(CallKind.VIRTUAL, csCallSite, csTarget))) {
                addReachable(csTarget);
                int cntParam = target.getParamCount();
                assert(cntParam == invoke.getInvokeExp().getArgCount());

                for (int i = 0; i < cntParam; ++i) {
                    CSVar varOutside = csManager.getCSVar(recvContext, invoke.getInvokeExp().getArg(i));
                    CSVar varInside = csManager.getCSVar(targetContext, target.getIR().getParam(i));
                    addPFGEdge(varOutside, varInside);
                }

                if (invoke.getLValue() != null) {
                    CSVar resultOutside = csManager.getCSVar(recvContext, invoke.getLValue());
                    for (Var returnVar : target.getIR().getReturnVars()) {
                        CSVar resultInside = csManager.getCSVar(targetContext, returnVar);
                        addPFGEdge(resultInside, resultOutside);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
