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
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private PointerFlowGraph taintPointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    public record TransferInstance(Invoke invoke, Context context, CSMethod csMethod, CSVar base) {
    }

    Solver(AnalysisOptions options, HeapModel heapModel, ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
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

    public void addWorkList(Pointer p, PointsToSet pts) {
        workList.addEntry(p, pts);
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        taintPointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
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

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (!callGraph.contains(csMethod)) {
            boolean isNew = callGraph.addReachableMethod(csMethod);

            StmtProcessor processor = new StmtProcessor(csMethod);

            csMethod.getMethod().getIR().forEach(stmt -> stmt.accept(processor));
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

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            // x = new ...()
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            Obj rawObj = heapModel.getObj(stmt);
            Context newContext = contextSelector.selectHeapContext(csMethod, rawObj);
            CSObj csObj = csManager.getCSObj(newContext, rawObj);
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));

            return null;
        }

        public Void visit(Copy stmt) {
            // x = y
            CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
            CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());

            addPFGEdge(csRVar, csLVar);

            return null;
        }

        public Void visit(LoadField stmt) {
            // x = T.f
            if (!stmt.isStatic()) {
                return null;
            }

            CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
            JField field = stmt.getFieldRef().resolve();
            StaticField staticField = csManager.getStaticField(field);

            addPFGEdge(staticField, csLVar);
            return null;
        }

        public Void visit(StoreField stmt) {
            // T.f = y
            if (!stmt.isStatic()) {
                return null;
            }

            CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());
            JField field = stmt.getFieldRef().resolve();
            StaticField staticField = csManager.getStaticField(field);

            addPFGEdge(csRVar, staticField);
            return null;
        }

        public Void visit(Invoke stmt) {
            /// static invoke only
            if (!stmt.isStatic()) {
                return null;
            }

            /// Tain Analysis
            taintAnalysis.checkSink(stmt, context);

            JMethod method = stmt.getMethodRef().resolve();
            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            Context newContext = contextSelector.selectContext(csCallSite, method);
            CSMethod csMethod = csManager.getCSMethod(newContext, method);

            Type resType = method.getReturnType();

            /// Taint Analysis: make new
            /// since taint object can be only made by source method
            /// sources are static, and can't be inter analysed
            if (taintAnalysis.isSource(method, resType)) {
                CSVar csVar = csManager.getCSVar(context, stmt.getResult());

                if(csVar != null){
                    Obj rawTaintObj = taintAnalysis.makeTaint(stmt, resType);
                    Context newHeapContext = contextSelector.selectHeapContext(csMethod, rawTaintObj);
                    CSObj csTaintObj = csManager.getCSObj(newHeapContext, rawTaintObj);

                    workList.addEntry(csVar, PointsToSetFactory.make(csTaintObj));
                }
            }
            /// transfer taint objs
            taintAnalysis.processTransfer(new TransferInstance(stmt, context, csMethod, null));
            /// Taint Analysis end

            Edge<CSCallSite, CSMethod> edge = new Edge<>(getCallKind(stmt), csCallSite, csMethod);

            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);

                List<CSVar> CSArgs = stmt.getInvokeExp().getArgs().stream().map(var -> csManager.getCSVar(context, var)).toList();
                List<CSVar> CSParams = method.getIR().getParams().stream().map(var -> csManager.getCSVar(newContext, var)).toList();

                for (int i = 0; i < CSArgs.size(); ++i) {
                    addPFGEdge(CSArgs.get(i), CSParams.get(i));
                }

                Var recv = stmt.getLValue();
                if (recv != null) {
                    List<CSVar> csMethodRets = method.getIR().getReturnVars().stream().map(var -> csManager.getCSVar(newContext, var)).toList();
                    CSVar csRecv = csManager.getCSVar(context, recv);
                    for (CSVar csRet : csMethodRets) {
                        addPFGEdge(csRet, csRecv);
                    }
                }
            }
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

    public void addTaintPFGEdge(Pointer source, Pointer target) {
        if (taintPointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                /// only add taint objs
                workList.addEntry(target, taintAnalysis.getTaintObjs(source.getPointsToSet()));
            }
        }
    }

    private void analysisImpl() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet diff = propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof CSVar csVar) {
                Context context = csVar.getContext();
                for (CSObj csObj : diff) {

                    for (LoadField stmt : csVar.getVar().getLoadFields()) {
                        CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
                        JField field = stmt.getFieldRef().resolve();

                        InstanceField csInstantField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(csInstantField, csLVar);
                    }
                    for (StoreField stmt : csVar.getVar().getStoreFields()) {
                        CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());
                        JField field = stmt.getFieldRef().resolve();

                        InstanceField csInstantField = csManager.getInstanceField(csObj, field);
                        addPFGEdge(csRVar, csInstantField);
                    }
                    for (LoadArray stmt : csVar.getVar().getLoadArrays()) {
                        CSVar csLVar = csManager.getCSVar(context, stmt.getLValue());
                        ArrayIndex arrIdx = csManager.getArrayIndex(csObj);

                        addPFGEdge(arrIdx, csLVar);
                    }
                    for (StoreArray stmt : csVar.getVar().getStoreArrays()) {
                        CSVar csRVar = csManager.getCSVar(context, stmt.getRValue());
                        ArrayIndex arrIdx = csManager.getArrayIndex(csObj);

                        addPFGEdge(csRVar, arrIdx);
                    }
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        analysisImpl();
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer n, PointsToSet pts) {
        // TODO - finish me

        PointsToSet diff = PointsToSetFactory.make();
        pts.getObjects().forEach(csObj -> {
            if (!n.getPointsToSet().contains(csObj)) {
                diff.addObject(csObj);
            }
        });

        if (!diff.isEmpty()) {
            n.getPointsToSet().addAll(diff);
            for (Pointer s : pointerFlowGraph.getSuccsOf(n)) {
                workList.addEntry(s, diff);
            }
            for (Pointer s : taintPointerFlowGraph.getSuccsOf(n)) {
                workList.addEntry(s, taintAnalysis.getTaintObjs(diff));
            }
        }

        return diff;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context context = recv.getContext();
        for (Invoke stmt : recv.getVar().getInvokes()) {
            JMethod method;
            if(taintAnalysis.isTaint(recvObj)){
                method = stmt.getMethodRef().resolve();
            }else{
                method = resolveCallee(recvObj, stmt);
            }

            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, method);
            CSMethod csMethod = csManager.getCSMethod(newContext, method);
            CSVar csMethodThis = csManager.getCSVar(newContext, method.getIR().getThis());

            workList.addEntry(csMethodThis, PointsToSetFactory.make(recvObj));
            Edge<CSCallSite, CSMethod> edge = new Edge<>(getCallKind(stmt), csCallSite, csMethod);

            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);
                List<CSVar> CSArgs = stmt.getInvokeExp().getArgs().stream().map(var -> csManager.getCSVar(context, var)).toList();
                List<CSVar> CSParams = method.getIR().getParams().stream().map(var -> csManager.getCSVar(newContext, var)).toList();

                for (int i = 0; i < CSArgs.size(); ++i) {
                    addPFGEdge(CSArgs.get(i), CSParams.get(i));
                }

                Var _recv = stmt.getLValue();
                if (_recv != null) {
                    List<CSVar> csMethodRets = method.getIR().getReturnVars().stream().map(var -> csManager.getCSVar(newContext, var)).toList();
                    CSVar csRecv = csManager.getCSVar(context, _recv);
                    for (CSVar csRet : csMethodRets) {
                        addPFGEdge(csRet, csRecv);
                    }
                }
            }
            /// taint Analysis
            taintAnalysis.processTransfer(new TransferInstance(stmt, context, csMethod, recv));
            taintAnalysis.checkSink(stmt, context, recv);
            /// taint obj transfer
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
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
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
