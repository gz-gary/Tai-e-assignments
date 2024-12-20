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

package pascal.taie.analysis.pta.plugin.taint;

import java.util.Set;
import java.util.TreeSet;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    public PointsToSet getTaintObjects(JMethod method, Invoke callSite) {
        PointsToSet taintObjects = PointsToSetFactory.make();
        for (Source source : config.getSources()) {
            if (source.method() == method) {
                taintObjects.addObject(
                    csManager.getCSObj(emptyContext, manager.makeTaint(callSite, source.type()))
                );
            }
        }
        return taintObjects;
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        CallGraph<CSCallSite, CSMethod> callgraph = result.getCSCallGraph();
        for (CSMethod csMethod : callgraph.getNodes()) {
            JMethod method = csMethod.getMethod();
            for (CSCallSite csCallSite : callgraph.getCallersOf(csMethod)) {
                for (Sink sink : config.getSinks()) {
                    if (sink.method() == method) {
                        int idx = sink.index();
                        CSVar csArg = csManager.getCSVar(
                            csCallSite.getContext(),
                            csCallSite.getCallSite().getInvokeExp().getArg(idx)
                        );
                        for (CSObj csObj : result.getPointsToSet(csArg)) {
                            if (manager.isTaint(csObj.getObject())) {
                                Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                                if (sourceCall != null) {
                                    Invoke sinkCall = csCallSite.getCallSite();
                                    taintFlows.add(new TaintFlow(sourceCall, sinkCall, idx));
                                }
                            }
                        }
                    }
                }
            }
        }
        // You could query pointer analysis results you need via variable result.
        return taintFlows;
    }
}
