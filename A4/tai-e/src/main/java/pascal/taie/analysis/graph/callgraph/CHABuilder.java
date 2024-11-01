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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import soot.coffi.class_element_value;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;
import java.util.LinkedHashSet;
import java.util.LinkedList;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> worklist = new LinkedList<>();
        worklist.offer(entry);

        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (!callGraph.addReachableMethod(method)) continue;

            for (Invoke callsite : callGraph.getCallSitesIn(method)) {
                CallKind callKind = CallKind.OTHER;
                if (callsite.isStatic()) callKind = CallKind.STATIC;
                if (callsite.isSpecial()) callKind = CallKind.SPECIAL;
                if (callsite.isInterface()) callKind = CallKind.INTERFACE;
                if (callsite.isVirtual()) callKind = CallKind.VIRTUAL;

                Set<JMethod> possiblMethods = resolve(callsite);
                for (JMethod target : possiblMethods) {
                    callGraph.addEdge(new Edge<Invoke,JMethod>(callKind, callsite, target));
                    worklist.offer(target);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> result = new LinkedHashSet<JMethod>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subSignature = methodRef.getSubsignature();
        JClass declClass = methodRef.getDeclaringClass();
        if (callSite.isStatic()) {
            result.add(declClass.getDeclaredMethod(subSignature));
        }
        if (callSite.isSpecial()) {
            result.add(dispatch(declClass, subSignature));
        }
        if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> queue = new ArrayDeque<JClass>();
            queue.offer(declClass);
            while (!queue.isEmpty()) {
                JClass jclass = queue.poll();
                assert jclass != null;

                result.add(dispatch(jclass, subSignature));
                for (JClass subClass : hierarchy.getDirectSubclassesOf(jclass)) {
                    if (!queue.contains(subClass)) {
                        queue.offer(subClass);
                    }
                }
                for (JClass subInterface : hierarchy.getDirectSubinterfacesOf(jclass)) {
                    if (!queue.contains(subInterface)) {
                        queue.offer(subInterface);
                    }
                }
                for (JClass implementor : hierarchy.getDirectImplementorsOf(jclass)) {
                    if (!queue.contains(implementor)) {
                        queue.offer(implementor);
                    }
                }
            }
        }
        result.remove(null);
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method == null || method.isAbstract()) {
            JClass superClass = jclass.getSuperClass();
            return superClass == null ? null : dispatch(superClass, subsignature);
        } else {
            return method;
        }
    }
}
