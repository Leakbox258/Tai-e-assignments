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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import static pascal.taie.ir.exp.ArithmeticExp.Op.*;
import static pascal.taie.ir.exp.ArithmeticExp.Op.DIV;
import static pascal.taie.ir.exp.ArithmeticExp.Op.REM;
import static pascal.taie.ir.exp.BitwiseExp.Op.*;
import static pascal.taie.ir.exp.ConditionExp.Op.*;
import static pascal.taie.ir.exp.ConditionExp.Op.GE;
import static pascal.taie.ir.exp.ShiftExp.Op.*;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            fact.update(var, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2)) {
                return v1;
            } else {
                return Value.getNAC();
            }
        } else {
            throw new AnalysisException("meetValue: can't match");
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact old_out = out.copy();

        out.copyFrom(in);

        /// canHoldInt
        stmt.getDef().ifPresent(lValue -> out.remove((Var) lValue));

        for (RValue rvalue : stmt.getUses()) {
            stmt.getDef().ifPresent(lValue ->
                    out.update((Var) lValue, evaluate(rvalue, in))
            );
        }

        return !out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp binary) {
            ///  thanks to ir
            Value lhs = in.get(binary.getOperand1());
            Value rhs = in.get(binary.getOperand2());

            if (lhs.isUndef() || rhs.isUndef()) {
                return Value.getUndef();
            } else if (lhs.isNAC() || rhs.isNAC()) {
                return Value.getNAC();
            }

            BinaryExp.Op op = binary.getOperator();

            int left = lhs.getConstant();
            int right = rhs.getConstant();

            int result = 0;
            if (op == ADD) {
                result = left + right;
            } else if (op == SUB) {
                result = left - right;
            } else if (op == MUL) {
                result = left * right;
            } else if (op == DIV) {
                if (right == 0) {
                    return Value.getUndef();
                }
                result = left / right;
            } else if (op == REM) {
                if (right == 0) {
                    return Value.getUndef();
                }
                result = left % right;
            } else if (op == OR) {
                result = left | right;
            } else if (op == AND) {
                result = left & right;
            } else if (op == XOR) {
                result = left ^ right;
            } else if (op == EQ) {
                if (left == right) {
                    result = 1;
                }
            } else if (op == NE) {
                if (left != right) {
                    result = 1;
                }
            } else if (op == LT) {
                if (left < right) {
                    result = 1;
                }
            } else if (op == GT) {
                if (left > right) {
                    result = 1;
                }
            } else if (op == LE) {
                if (left <= right) {
                    result = 1;
                }
            } else if (op == GE) {
                if (left >= right) {
                    result = 1;
                }
            } else if (op == SHL) {
                result = left << right;
            } else if (op == SHR) {
                result = left >> right;
            } else if (op == USHR) {
                result = left >>> right;
            } else {
                throw new IllegalArgumentException("Unknown op: " + op);
            }

            return Value.makeConstant(result);
        } else {
            ///  InvokeVirtual
            return Value.getNAC();
        }
    }
}
