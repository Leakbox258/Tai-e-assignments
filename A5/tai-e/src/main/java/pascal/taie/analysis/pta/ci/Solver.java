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
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

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
        // TODO - finish me

        if (!callGraph.contains(method)) {
            boolean isNew = callGraph.addReachableMethod(method);

            method.getIR().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            /// x = new T()
            Obj obj = heapModel.getObj(stmt);
            VarPtr varptr = pointerFlowGraph.getVarPtr(stmt.getLValue());

            workList.addEntry(varptr, new PointsToSet(obj));
            return null;
        }

        public Void visit(Copy stmt) {
            ///  y = x
            Pointer source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            Pointer target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        public Void visit(LoadField stmt) {
            /// x = y.field
            Var lvar = stmt.getLValue();

            VarPtr lvarptr = pointerFlowGraph.getVarPtr(lvar);

            JField field = stmt.getFieldRef().resolve();
            boolean isStatic = stmt.isStatic();
            if (isStatic) {
                StaticField stField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(stField, lvarptr);
            }
            return null;
        }

        public Void visit(StoreField stmt) {
            /// y.field = x
            Var rvar = stmt.getRValue();

            VarPtr rvarptr = pointerFlowGraph.getVarPtr(rvar);

            JField field = stmt.getFieldRef().resolve();
            boolean isStatic = stmt.isStatic();
            if (isStatic) {
                StaticField stField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(rvarptr, stField);
            }
            return null;
        }

        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            ///  static invoke
            JMethod method = stmt.getMethodRef().resolve();

            Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(stmt), stmt, method);
            if (callGraph.addEdge(edge)) {
                addReachable(method);
                for (int idx = 0; idx < method.getParamCount(); ++idx) {
                    Pointer source = pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(idx));
                    Pointer target = pointerFlowGraph.getVarPtr(method.getIR().getVar(idx));
                    addPFGEdge(source, target);
                }

                /// todo...
                List<Var> methodRets = method.getIR().getReturnVars();
                if (!methodRets.isEmpty()) {
                    Var ret = stmt.getLValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(methodRets.get(0)), pointerFlowGraph.getVarPtr(ret));
                }
            }

            return null;
        }

        public Void visit(Return stmt) {
            /// $temp = return x
            Var rvar = stmt.getValue();

            if (rvar == null) {
                return null;
            }

            JMethod currentMethod = rvar.getMethod();

            if (currentMethod.getIR().getReturnVars().isEmpty()) {
                return null;
            }

            Var methodRet = currentMethod.getIR().getReturnVars().get(0);

            if(rvar == methodRet){
                return null;
            }

            /// circle call between methods
            Pointer source = pointerFlowGraph.getVarPtr(rvar);
            Pointer target = pointerFlowGraph.getVarPtr(methodRet);
            addPFGEdge(source, target);

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me

        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me

        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();

            PointsToSet diff = propagate(n, pts);

            if (n instanceof VarPtr varptr) {
                Var var = varptr.getVar();

                for (Obj o : diff) {
                    for (StoreField stmt : var.getStoreFields()) {
                        JField field = stmt.getFieldRef().resolve();
                        VarPtr rvarptr = pointerFlowGraph.getVarPtr(stmt.getRValue());

                        addPFGEdge(rvarptr, pointerFlowGraph.getInstanceField(o, field));
                    }
                    for (LoadField stmt : var.getLoadFields()) {
                        JField field = stmt.getFieldRef().resolve();
                        VarPtr lvarptr = pointerFlowGraph.getVarPtr(stmt.getLValue());

                        addPFGEdge(pointerFlowGraph.getInstanceField(o, field), lvarptr);
                    }
                    for (StoreArray stmt : var.getStoreArrays()) {
                        VarPtr rvarptr = pointerFlowGraph.getVarPtr(stmt.getRValue());

                        addPFGEdge(rvarptr, pointerFlowGraph.getArrayIndex(o));
                    }
                    for (LoadArray stmt : var.getLoadArrays()) {
                        VarPtr lvarptr = pointerFlowGraph.getVarPtr(stmt.getLValue());

                        addPFGEdge(pointerFlowGraph.getArrayIndex(o), lvarptr);
                    }
                    processCall(var, o);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer n, PointsToSet pts) {
        // TODO - finish me

        PointsToSet diff = new PointsToSet(pts);
        diff.removeAll(n.getPointsToSet());

        if (!diff.isEmpty()) {
            n.getPointsToSet().addAll(diff);
            for (Pointer target : pointerFlowGraph.getSuccsOf(n)) {
                workList.addEntry(target, diff);
            }
        }

        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke stmt : var.getInvokes()) {

            JMethod method = resolveCallee(recv, stmt);

            /// cover static & instance invoke?
            Pointer varPtr = pointerFlowGraph.getVarPtr(method.getIR().getThis());
            workList.addEntry(varPtr, new PointsToSet(recv));

            Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(stmt), stmt, method);
            if (callGraph.addEdge(edge)) {
                addReachable(method);
                for (int idx = 0; idx < method.getParamCount(); ++idx) {
                    Pointer source = pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(idx));
                    Pointer target = pointerFlowGraph.getVarPtr(method.getIR().getParam(idx));
                    addPFGEdge(source, target);
                }

                /// todo...
                List<Var> methodRets = method.getIR().getReturnVars();
                if (!methodRets.isEmpty()) {
                    Var ret = stmt.getLValue();
                    if (ret != null) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(methodRets.get(0)), pointerFlowGraph.getVarPtr(ret));
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
}
