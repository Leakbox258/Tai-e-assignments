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

        sinkInstances.forEach(sinkInstance -> {
            CSVar base = sinkInstance.csVar;
            Invoke stmt = sinkInstance.invoke;
            Context context = sinkInstance.context;

            sinkInstance.indexes.forEach(idx -> {
                Set<Obj> pts = new HashSet<>();
                if (idx == -1) { // base
                    pts = result.getPointsToSet(base).stream().map(CSObj::getObject).collect(Collectors.toSet());
                } else if (idx >= 0) {
                    CSVar csArg = solver.getCSManager().getCSVar(context, stmt.getInvokeExp().getArg(idx));
                    pts = result.getPointsToSet(csArg).stream().map(CSObj::getObject).collect(Collectors.toSet());
                }

                Set<Obj> taintObjs = getTaintObj(pts);

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

    public Obj makeTaint(Invoke source, Type ty) {
        return manager.makeTaint(source, ty);
    }

    public List<Integer> FromTransfer(JMethod method) {
        List<Integer> list = new ArrayList<>();

        config.getTransfers().forEach(trans -> {
            if (trans.method() == method) {
                list.add(trans.from());
            }
        });

        return list;
    }

    public List<Integer> ToTransfer(JMethod method) {
        List<Integer> list = new ArrayList<>();

        config.getTransfers().forEach(trans -> {
            if (trans.method() == method) {
                list.add(trans.to());
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

    private Set<Obj> getTaintObj(Set<Obj> pts) {
        return pts.stream().filter(manager::isTaint).collect(Collectors.toSet());
    }

    public void processTransfer(Invoke stmt, Context context, CSMethod csMethod) {
        Var result = stmt.getResult();
        List<Var> args = stmt.getInvokeExp().getArgs();
        JMethod method = stmt.getMethodRef().resolve();

        Set<CSObj> taintCSObjs = new HashSet<>();
        boolean tainted = FromTransfer(method).stream().anyMatch(idx -> {
            if (idx >= 0) {
                /// arguments
                CSVar csVar = csManager.getCSVar(context, args.get(idx));
                if (hasTaint(csVar.getPointsToSet())) {
                    Set<CSObj> taints = csVar.getPointsToSet().getObjects().stream().filter(csObj -> manager.isTaint(csObj.getObject())).collect(Collectors.toSet());
                    taintCSObjs.addAll(taints);
                    return true;
                } else {
                    return false;
                }
            } else if (idx == -1) {
                /// static, cant be base
                return false;
            } else if (idx == -2) {
                /// From cant be result
                return false;
            } else{
                return false;
            }
        });

        if (tainted) {
            ToTransfer(method).forEach(idx -> {
                CSVar csVar;
                PointsToSet pts = PointsToSetFactory.make(); // ?
                if (idx == -1) {
                    /// static, cant be base
                    csVar = null;
                } else if (idx == -2) {
                    /// if is -2, then result is always valid
                    csVar = csManager.getCSVar(context, result);
                } else {
                    /// args?
                    csVar = csManager.getCSVar(context, args.get(idx));
                }
                taintCSObjs.forEach(csObj -> {
                    /// a new type
                    Obj rawTaintObj = makeTaint(manager.getSourceCall(csObj.getObject()), csVar.getType());
                    Context newHeapContext = solver.getContextSelector().selectHeapContext(csMethod, rawTaintObj);
                    CSObj csTaintObj = csManager.getCSObj(newHeapContext, rawTaintObj);
                    pts.addObject(csTaintObj);
                });

                solver.addWorkList(csVar, pts);
            });
        }

//        return hasTaint;
    }

    public void processTransfer(Invoke stmt, Context context, CSMethod csMethod, CSVar base) {
        Var result = stmt.getResult();
        List<Var> args = stmt.getInvokeExp().getArgs();
        JMethod method = stmt.getMethodRef().resolve();

        Set<CSObj> taintCSObjs = new HashSet<>();
        boolean tainted = FromTransfer(method).stream().anyMatch(idx -> {
            if (idx >= 0) {
                /// arguments
                CSVar csVar = csManager.getCSVar(context, args.get(idx));
                if (hasTaint(csVar.getPointsToSet())) {
                    Set<CSObj> taints = csVar.getPointsToSet().getObjects().stream().filter(csObj -> manager.isTaint(csObj.getObject())).collect(Collectors.toSet());
                    taintCSObjs.addAll(taints);
                    return true;
                } else {
                    return false;
                }
            } else if (idx == -1) {
                if (hasTaint(base.getPointsToSet())) {
                    Set<CSObj> taints = base.getPointsToSet().getObjects().stream().filter(csObj -> manager.isTaint(csObj.getObject())).collect(Collectors.toSet());
                    taintCSObjs.addAll(taints);
                    return true;
                } else {
                    return false;
                }
            } else if (idx == -2) {
                /// From cant be result
                return false;
            }
            else{
                return false;
            }
        });

        if (tainted) {
            ToTransfer(method).forEach(idx -> {
                CSVar csVar;
                PointsToSet pts = PointsToSetFactory.make();
                if (idx == -1) {
                    csVar = base;
                } else if (idx == -2) {
                    /// if is -2, then result is always valid
                    csVar = csManager.getCSVar(context, result);
                } else {
                    /// args?
                    csVar = csManager.getCSVar(context, args.get(idx));
                }
                taintCSObjs.forEach(csObj -> {
                    Obj rawTaintObj = makeTaint(manager.getSourceCall(csObj.getObject()), csVar.getType());
                    Context newHeapContext = solver.getContextSelector().selectHeapContext(csMethod, rawTaintObj);
                    CSObj csTaintObj = csManager.getCSObj(newHeapContext, rawTaintObj);
                    pts.addObject(csTaintObj);
                });

                solver.addWorkList(csVar, pts);
            });
        }

//        return hasTaint;
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