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
import pascal.taie.language.classes.*;
import pascal.taie.util.AnalysisException;

import javax.annotation.Nullable;
import java.lang.invoke.CallSite;
import java.util.*;

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

    private CallKind getCallKind(Invoke cs) {
        if (cs.isSpecial()) {
            return CallKind.SPECIAL;
        } else if (cs.isStatic()) {
            return CallKind.STATIC;
        } else if (cs.isInterface()) {
            return CallKind.INTERFACE;
        } else if (cs.isVirtual()) {
            return CallKind.VIRTUAL;
        } else if (cs.isDynamic()) {
            return CallKind.DYNAMIC;
        } else {
            return CallKind.OTHER;
        }
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Vector<JMethod> worklist = new Vector<>();
        worklist.add(entry);

        while (!worklist.isEmpty()) {
            JMethod method = worklist.remove(0);

            if (callGraph.contains(method)) {
                continue;
            }

            callGraph.addReachableMethod(method);
            for (Invoke cs : callGraph.getCallSitesIn(method)) {
                Set<JMethod> T = resolve(cs);
                for (JMethod m : T) {
                    Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(cs), cs, m);
                    callGraph.addEdge(edge);
                    if (!callGraph.contains(m)) {
                        worklist.add(m);
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me

        Set<JMethod> T = new LinkedHashSet<>();

        Subsignature sig = callSite.getMethodRef().getSubsignature();

        if (callSite.isVirtual() || callSite.isInterface()) {
            Vector<JClass> deque = new Vector<>();
            deque.add(callSite.getMethodRef().getDeclaringClass());

            while (!deque.isEmpty()) {
                JClass jclass = deque.remove(0);

                T.add(dispatch(jclass, sig)); // maybe null

                if (jclass.isInterface()) {
                    deque.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                    deque.addAll(hierarchy.getDirectImplementorsOf(jclass));
                } else {
                    deque.addAll(hierarchy.getDirectSubclassesOf(jclass));
                }
            }
        } else {
            T.add(dispatch(callSite.getMethodRef().getDeclaringClass(), sig));
        }

        T.remove(null);

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    @Nullable
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me

        JClass superClass = jclass;
        JMethod dispatchMethod = null;

        while (superClass != null) {
            dispatchMethod = superClass.getDeclaredMethod(subsignature);

            if (dispatchMethod != null && !dispatchMethod.isAbstract()) {
                break;
            }

            superClass = superClass.getSuperClass();
        }

        return dispatchMethod;
    }
}
