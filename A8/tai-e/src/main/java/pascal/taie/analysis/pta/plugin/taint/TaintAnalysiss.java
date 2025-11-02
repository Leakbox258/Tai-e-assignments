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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;
import java.util.List;
import java.util.stream.Collectors;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;
    /// ?
    private final Context emptyContext;

    ///
    record SinkInstance(Invoke invoke, Context context, CSVar csVar, Set<Integer> indexes) {
    }

    private final Set<SinkInstance> sinkInstances;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(solver.getOptions().getString("taint-config"), World.get().getClassHierarchy(), World.get().getTypeSystem());
        logger.info(config);
        sinkInstances = new LinkedHashSet<>();
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

//        Set<CSVar> taintCSVars = result.getCSVars().stream().filter(csVar -> hasTaint(csVar.getPointsToSet())).collect(Collectors.toSet());

        sinkInstances.forEach(sinkInstance -> {
            CSVar base = sinkInstance.csVar;
            Invoke stmt = sinkInstance.invoke;
            Context context = sinkInstance.context;

            sinkInstance.indexes.forEach(idx -> {
                Set<Obj> pts = new HashSet<>();
                if (idx == TaintTransfer.BASE) { // base
                    pts = result.getPointsToSet(base).stream().map(CSObj::getObject).collect(Collectors.toSet());
                } else if (idx >= 0) {
                    CSVar csArg = csManager.getCSVar(context, stmt.getInvokeExp().getArg(idx));
                    pts = result.getPointsToSet(csArg).stream().map(CSObj::getObject).collect(Collectors.toSet());
                }

                Set<Obj> taintObjs = getTaintObjs(pts);

                if (hasTaint(pts)) {
                    taintObjs.forEach(obj -> {
                        taintFlows.add(new TaintFlow(manager.getSourceCall(obj), stmt, idx));
                    });
                }
            });
        });

        return taintFlows;
    }

    /// interface
    public boolean isSource(JMethod method, Type type) {
        return config.getSources().contains(new Source(method, type));
    }

    public boolean isTaint(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Obj makeTaint(Invoke source, Type ty) {
        return manager.makeTaint(source, ty);
    }

    private record FromTo(Integer from, Integer to) {
    }

    private List<FromTo> FromToTransfer(JMethod method) {
        List<FromTo> list = new LinkedList<>();

        config.getTransfers().forEach(trans -> {
            if (trans.method() == method) {
                list.add(new FromTo(trans.from(), trans.to()));
            }
        });

        return list;
    }

    public boolean hasTaint(PointsToSet pts) {
        return pts.getObjects().stream().anyMatch(csObj -> manager.isTaint(csObj.getObject()));
    }

    public boolean hasTaint(Set<Obj> pts) {
        return pts.stream().anyMatch(manager::isTaint);
    }

    public Set<Obj> getTaintObjs(Set<Obj> pts) {
        return pts.stream().filter(manager::isTaint).collect(Collectors.toSet());
    }

    public PointsToSet getTaintObjs(PointsToSet pts) {
        PointsToSet newPts = PointsToSetFactory.make();
        pts.forEach(csObj -> {
            if (manager.isTaint(csObj.getObject())) newPts.addObject(csObj);
        });
        return newPts;
    }

    public void processTransfer(Solver.TransferInstance instance) {
        Invoke invoke = instance.invoke();
        Context context = instance.context();
        CSMethod method = instance.csMethod();
        CSVar csVar = instance.base();

        processTransfer(invoke, context, method, csVar);
    }

    private void processTransfer(Invoke stmt, Context context, CSMethod csMethod, CSVar base) {
        Var result = stmt.getResult();
        List<Var> args = stmt.getInvokeExp().getArgs();
        JMethod method = csMethod.getMethod();

        FromToTransfer(method).forEach(fromTo -> {
            CSVar source = null, target = null;
            if (fromTo.from >= 0 && fromTo.to == TaintTransfer.RESULT) {
                /// arg-to-result
                source = csManager.getCSVar(context, args.get(fromTo.from));
                target = csManager.getCSVar(context, result);
            } else if (fromTo.from >= 0 && fromTo.to == TaintTransfer.BASE) {
                ///  arg-to-base
                source = csManager.getCSVar(context, args.get(fromTo.from));
                target = base;
            } else if (fromTo.from == TaintTransfer.BASE && fromTo.to == TaintTransfer.RESULT) {
                ///  base-to-result
                source = base;
                target = csManager.getCSVar(context, result);
            }

            if (source != null && target != null) {
                solver.addTaintPFGEdge(source, target);
                PointsToSet taintPts = getTaintObjs(source.getPointsToSet());
                PointsToSet newPts = PointsToSetFactory.make();
                Type ty = target.getType();
                taintPts.forEach(taintObj -> {
                    /// considering changeable type
                    Obj rawTainObj = makeTaint(manager.getSourceCall(taintObj.getObject()), ty);
                    Context heapContext = solver.getContextSelector().selectHeapContext(csMethod, rawTainObj);
                    newPts.addObject(csManager.getCSObj(heapContext, rawTainObj));
                });

                solver.addWorkList(target, newPts);
            }

        });

    }

    public void checkSink(Invoke stmt, Context context) {
        JMethod method = stmt.getMethodRef().resolve();
        Set<Integer> indexes = new LinkedHashSet<>();

        config.getSinks().forEach(sink -> {
            if (sink.method() == method) {
                indexes.add(sink.index());
            }
        });

        if (!indexes.isEmpty()) sinkInstances.add(new SinkInstance(stmt, context, null, indexes));
    }

    public void checkSink(Invoke stmt, Context context, CSVar base) {
        JMethod method = stmt.getMethodRef().resolve();
        Set<Integer> indexes = new LinkedHashSet<>();

        config.getSinks().forEach(sink -> {
            if (sink.method() == method) {
                indexes.add(sink.index());
            }
        });

        if (!indexes.isEmpty()) sinkInstances.add(new SinkInstance(stmt, context, base, indexes));
    }

}