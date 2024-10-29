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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        CPFact boundary = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param)) {
                boundary.update(param, Value.getNAC());
            }
        }
        return boundary;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var v : fact.keySet()) {
            target.update(v, meetValue(fact.get(v), target.get(v)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        assert v1.isConstant();
        assert v2.isConstant();
        return v1.getConstant() == v2.getConstant() ? Value.makeConstant(v1.getConstant()) : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact in_copy = in.copy();
        if (stmt instanceof DefinitionStmt definition_stmt) {
            if (stmt.getDef().isPresent() && (stmt.getDef().get() instanceof Var def)) {
                if (canHoldInt(def)) {
                    Value def_v = evaluate(definition_stmt.getRValue(), in);
                    in_copy.update(def, def_v);
                }
            }
        }
        return out.copyFrom(in_copy);
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
        if (exp instanceof Var exp_Var) {
            return in.get(exp_Var);
        } else if (exp instanceof IntLiteral exp_IntLiteral) {
            return Value.makeConstant(exp_IntLiteral.getValue());
        } else if (exp instanceof BinaryExp exp_BinaryExp) {
            Var operand1 = exp_BinaryExp.getOperand1();
            Var operand2 = exp_BinaryExp.getOperand2();
            if (!canHoldInt(operand1) || !canHoldInt(operand2)) return Value.getNAC();

            Value value1 = in.get(operand1);
            Value value2 = in.get(operand2);

            if (value1.isUndef() || value2.isUndef()) return Value.getUndef();

            if (value1.isConstant() && value2.isConstant()) {
                int i1 = value1.getConstant();
                int i2 = value2.getConstant();
                if (exp_BinaryExp instanceof ArithmeticExp exp_ArithmeticExp) {
                    switch (exp_ArithmeticExp.getOperator()) {
                        case ADD: return Value.makeConstant(i1 + i2);
                        case SUB: return Value.makeConstant(i1 - i2);
                        case MUL: return Value.makeConstant(i1 * i2);
                        case DIV:
                            if (i2 == 0) return Value.getUndef();
                            else return Value.makeConstant(i1 / i2);
                        case REM:
                            if (i2 == 0) return Value.getUndef();
                            else return Value.makeConstant(i1 % i2);
                        default:
                            return Value.getNAC();
                    }
                } else if (exp_BinaryExp instanceof ConditionExp exp_ConditionExp) {
                    switch (exp_ConditionExp.getOperator()) {
                        case EQ: return Value.makeConstant((i1 == i2) ? 1 : 0);
                        case NE: return Value.makeConstant((i1 != i2) ? 1 : 0);
                        case LT: return Value.makeConstant((i1 < i2) ? 1 : 0);
                        case GT: return Value.makeConstant((i1 > i2) ? 1 : 0);
                        case LE: return Value.makeConstant((i1 <= i2) ? 1 : 0);
                        case GE: return Value.makeConstant((i1 >= i2) ? 1 : 0);
                        default:
                            return Value.getNAC();
                    }
                } else if (exp_BinaryExp instanceof ShiftExp exp_ShiftExp) {
                    switch (exp_ShiftExp.getOperator()) {
                        case SHL: return Value.makeConstant(i1 << i2);
                        case SHR: return Value.makeConstant(i1 >> i2);
                        case USHR: return Value.makeConstant(i1 >>> i2);
                        default:
                            return Value.getNAC();
                    }
                } else if (exp_BinaryExp instanceof BitwiseExp exp_BitwiseExp) {
                    switch (exp_BitwiseExp.getOperator()) {
                        case AND: return Value.makeConstant(i1 & i2);
                        case OR: return Value.makeConstant(i1 | i2);
                        case XOR: return Value.makeConstant(i1 ^ i2);
                        default:
                            return Value.getNAC();
                    }
                } else return Value.getNAC();
            } else if (value1.isNAC() || value2.isNAC()) {
                /* Corner case for NAC / 0 and NAC % 0 */
                if (value1.isNAC() && value2.isConstant() && value2.getConstant() == 0) {
                    if (exp_BinaryExp instanceof ArithmeticExp exp_ArithmeticExp) {
                        if (exp_ArithmeticExp.getOperator() == ArithmeticExp.Op.DIV
                            || exp_ArithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                            return Value.getUndef();
                        }
                    }
                }
                return Value.getNAC();
            } else return Value.getNAC();
        } else return Value.getNAC();
    }
}
