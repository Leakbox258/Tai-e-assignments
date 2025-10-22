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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;
import java.util.Vector;
import java.util.function.Consumer;
import java.util.function.Function;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        Vector<Stmt> deque = new Vector<>();
        Set<Stmt> useful = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        deque.add(cfg.getEntry());

        Consumer<Stmt> addDeque = (Stmt stmt) -> {
            if (!useful.contains(stmt)) {
                ((Vector<Stmt>) deque).add(stmt);
            }
        };

        Consumer<Set<Stmt>> addAllDeque = (Set<Stmt> stmts) -> {
            for (Stmt stmt : stmts) {
                if (!useful.contains(stmt)) {
                    ((Vector<Stmt>) deque).add(stmt);
                }
            }
        };

        while (!deque.isEmpty()) {
            Stmt stmt = deque.remove(0);

            if (stmt instanceof If if_stmt) {
                // assume if_stmt is usefully even if with constant cond
                useful.add(stmt);
                /// branch unreachable

                ConditionExp cond = if_stmt.getCondition();
                Value cond_value = evaluateCondExpr(cond, constants.getInFact(if_stmt));

                if (cond_value.isNAC()) {
                    addAllDeque.accept(cfg.getSuccsOf(stmt));
                } else {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (cond_value.getConstant() == 0 && edge.getKind() == Edge.Kind.IF_FALSE
                                || cond_value.getConstant() == 1 && edge.getKind() == Edge.Kind.IF_TRUE) {
                            addDeque.accept(edge.getTarget());
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt switch_stmt) {
                /// branch unreachable

                useful.add(stmt);

                Var cond = switch_stmt.getVar();
                Value cond_value = constants.getInFact(switch_stmt).get(cond);

                if (cond_value.isConstant()) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == cond_value.getConstant()) {
                            addDeque.accept(edge.getTarget());
                            break;
                        } else if(edge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            // assume this is the last edge to be iterated
                            // Edge.Kind.SWITCH_CASE
                            addDeque.accept(edge.getTarget());
                        }
                    }
                } else {
                    addAllDeque.accept(cfg.getSuccsOf(stmt));
                }
            } else if (stmt instanceof AssignStmt<?, ?> assign_stmt) {
                // check if side effect
                boolean sideEffect = false;
                for (RValue rvalue : assign_stmt.getUses()) {
                    sideEffect |= !hasNoSideEffect(rvalue);
                }
                if (sideEffect) {
                    useful.add(assign_stmt);
                    addAllDeque.accept(cfg.getSuccsOf(stmt));
                    continue;
                }

                // the def of assignment won't be empty
                if (liveVars.getOutFact(assign_stmt).contains((Var) assign_stmt.getDef().get())) {
                    useful.add(assign_stmt);
                }
                addAllDeque.accept(cfg.getSuccsOf(stmt));

            } else if (stmt instanceof Return) {
                useful.add(stmt);
            } else {
                useful.add(stmt);
                addAllDeque.accept(cfg.getSuccsOf(stmt));
            }
        }

        useful.add(cfg.getExit());

        /// control unreachable
        for (Stmt stmt : cfg) {
            if (!useful.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    /**
     * @return Value after evaluate a CondExpr
     */
    private static Value evaluateCondExpr(ConditionExp cond, CPFact in) {
        ConditionExp.Op op = cond.getOperator();

        Value rhs = in.get(cond.getOperand1());
        Value lhs = in.get(cond.getOperand2());

        boolean res = false;
        if (rhs.isConstant() || lhs.isConstant()) {
            switch (op) {
                case EQ -> res = rhs.getConstant() == lhs.getConstant();
                case NE -> res = rhs.getConstant() != lhs.getConstant();
                case LT -> res = rhs.getConstant() < lhs.getConstant();
                case GT -> res = rhs.getConstant() > lhs.getConstant();
                case LE -> res = rhs.getConstant() <= lhs.getConstant();
                case GE -> res = rhs.getConstant() >= lhs.getConstant();
            }

            return Value.makeConstant(res ? 1 : 0);
        }

        /// never mind is NAC or UNDEF
        return Value.getNAC();
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
