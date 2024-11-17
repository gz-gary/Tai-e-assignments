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

package pascal.taie.analysis.dataflow.inter;

import java.util.LinkedList;
import java.util.Queue;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        this.workList = new LinkedList<>();
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        for (Node node : icfg) {
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(entryMethod -> {
            Node entry = icfg.getEntryOf(entryMethod);
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
    }

    private void doSolve() {
        workList.clear();
        for (Node node : icfg) workList.offer(node);

        while (!workList.isEmpty()) {
            Node node = workList.poll();
            assert node != null;

            Fact meet_of_all_preds = analysis.newInitialFact();
            for (ICFGEdge<Node> edge : icfg.getInEdgesOf(node)) {
                Node pred = edge.getSource();
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(pred)), meet_of_all_preds);
            }
            result.setInFact(node, meet_of_all_preds);

            boolean if_out_changed = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if (if_out_changed) {
                for (Node succ : icfg.getSuccsOf(node)) {
                    workList.offer(succ);
                }
            }
        }
    }
}
