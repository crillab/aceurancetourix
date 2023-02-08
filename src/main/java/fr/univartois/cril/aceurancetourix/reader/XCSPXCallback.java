/**
 * Sat4j-CSP, a CSP solver based on the Sat4j platform.
 * Copyright (c) 2021-2022 - Exakis Nelite, Univ Artois & CNRS.
 * All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library.
 * If not, see {@link http://www.gnu.org/licenses}.
 */

package fr.univartois.cril.aceurancetourix.reader;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.xcsp.common.Condition;
import org.xcsp.common.Condition.ConditionIntset;
import org.xcsp.common.Condition.ConditionIntvl;
import org.xcsp.common.Constants;
import org.xcsp.common.Types.TypeArithmeticOperator;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeEqNeOperator;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.Types.TypeFlag;
import org.xcsp.common.Types.TypeLogicalOperator;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.Types.TypeUnaryArithmeticOperator;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.parser.callbacks.XCallbacks2;
import org.xcsp.parser.entries.XConstraints.XGroup;
import org.xcsp.parser.entries.XVariables.XVarInteger;

import fr.univartois.cril.aceurancetourix.JUniverseAceProblemAdapter;
import fr.univartois.cril.juniverse.core.UniverseContradictionException;
import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;
import fr.univartois.cril.juniverse.csp.intension.IIntensionConstraint;
import fr.univartois.cril.juniverse.csp.operator.UniverseArithmeticOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseBooleanOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator;

/**
 * The UglyXCallback is an implementation of {@link XCallbacks2} that hides all
 * the gory implementation details required by this interface to make easier and
 * more flexible the parsing of XCSP3 instances.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
final class XCSPXCallback implements XCallbacks2 {

    /**
     * A map for translating a {@link TypeArithmeticOperator} to an
     * {@link ArithmeticOperator}.
     */
    private static final Map<TypeArithmeticOperator, UniverseArithmeticOperator> TYPE_ARITH_OP_TO_ARITH_OP = Map.of(
            TypeArithmeticOperator.ADD, UniverseArithmeticOperator.ADD,
            TypeArithmeticOperator.DIST, UniverseArithmeticOperator.DIST,
            TypeArithmeticOperator.DIV, UniverseArithmeticOperator.DIV,
            TypeArithmeticOperator.MOD, UniverseArithmeticOperator.MOD,
            TypeArithmeticOperator.MUL, UniverseArithmeticOperator.MULT,
            TypeArithmeticOperator.POW, UniverseArithmeticOperator.POW,
            TypeArithmeticOperator.SUB, UniverseArithmeticOperator.SUB);

    private static final Map<TypeUnaryArithmeticOperator, UniverseArithmeticOperator> TYPE_UNARY_ARITH_OP_TO_ARITH_OP = Map.of(
            TypeUnaryArithmeticOperator.ABS, UniverseArithmeticOperator.ABS,
            TypeUnaryArithmeticOperator.NEG, UniverseArithmeticOperator.NEG,
            TypeUnaryArithmeticOperator.SQR, UniverseArithmeticOperator.SQR);

    /**
     * A map for translating a {@link TypeLogicalOperator} to a {@link BooleanOperator}.
     */
    private static final Map<TypeLogicalOperator, UniverseBooleanOperator> TYPE_LOGIC_OP_TO_BOOL_OP = Map.of(
            TypeLogicalOperator.AND, UniverseBooleanOperator.AND,
            TypeLogicalOperator.IFF, UniverseBooleanOperator.EQUIV,
            TypeLogicalOperator.IMP, UniverseBooleanOperator.IMPL,
            TypeLogicalOperator.OR, UniverseBooleanOperator.OR,
            TypeLogicalOperator.XOR, UniverseBooleanOperator.XOR);

    /**
     * A map for translating a {@link TypeConditionOperatorRel} to a
     * {@link UniverseRelationalOperator}.
     */
    private static final Map<TypeConditionOperatorRel, UniverseRelationalOperator> TYPE_COND_OP_REL_TO_REL_OP = Map.of(
            TypeConditionOperatorRel.LT, UniverseRelationalOperator.LT,
            TypeConditionOperatorRel.LE, UniverseRelationalOperator.LE,
            TypeConditionOperatorRel.EQ, UniverseRelationalOperator.EQ,
            TypeConditionOperatorRel.NE, UniverseRelationalOperator.NEQ,
            TypeConditionOperatorRel.GT, UniverseRelationalOperator.GT,
            TypeConditionOperatorRel.GE, UniverseRelationalOperator.GE);

    /**
     * A map for translating a {@link TypeExpr} to a {@link UniverseRelationalOperator}.
     */
    private static final Map<TypeExpr, UniverseRelationalOperator> TYPE_EXPR_TO_REL_OP = Map.of(
            TypeExpr.LT, UniverseRelationalOperator.LT,
            TypeExpr.LE, UniverseRelationalOperator.LE,
            TypeExpr.EQ, UniverseRelationalOperator.EQ,
            TypeExpr.NE, UniverseRelationalOperator.NEQ,
            TypeExpr.GT, UniverseRelationalOperator.GT,
            TypeExpr.GE, UniverseRelationalOperator.GE);

    /**
     * A map for translating a {@link TypeOperatorRel} to a {@link UniverseRelationalOperator}.
     */
    private static final Map<TypeOperatorRel, UniverseRelationalOperator> TYPE_OP_REL_TO_REL_OP = Map.of(
            TypeOperatorRel.LT, UniverseRelationalOperator.LT,
            TypeOperatorRel.LE, UniverseRelationalOperator.LE,
            TypeOperatorRel.GT, UniverseRelationalOperator.GT,
            TypeOperatorRel.GE, UniverseRelationalOperator.GE);

    /**
     * A map for translating a {@link TypeConditionOperatorSet} to a
     * {@link UniverseSetBelongingOperator}.
     */
    private static final Map<TypeConditionOperatorSet, UniverseSetBelongingOperator> TYPE_COND_OP_SET_TO_SET_OP = Map.of(
            TypeConditionOperatorSet.IN, UniverseSetBelongingOperator.IN,
            TypeConditionOperatorSet.NOTIN, UniverseSetBelongingOperator.NOT_IN);

    /**
     * The listener to notify while reading an XCSP3 instance.
     */
    private IUniverseCSPSolver listener;

    /**
     * The implem object required for parsing XCSP3 instances.
     */
    private Implem implem;

    /**
     * Creates a new UglyXCallback.
     *
     * @param listener The listener to notify while reading an XCSP3 instance.
     */
    XCSPXCallback(IUniverseCSPSolver listener) {
        this.listener = listener;
        this.implem = new Implem(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks#implem()
     */
    @Override
    public Implem implem() {
        return implem;
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#unimplementedCase(java.lang.Object[])
     */
    @Override
    public Object unimplementedCase(Object... objects) {
        throw new UnsupportedOperationException();
    }
    
    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#beginGroup(org.xcsp.parser.entries.XConstraints.XGroup)
     */
    @Override
    public void beginGroup(XGroup g) {
       JUniverseAceProblemAdapter.currentGroup++;
       JUniverseAceProblemAdapter.inGroup=true;
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#endGroup(org.xcsp.parser.entries.XConstraints.XGroup)
     */
    @Override
    public void endGroup(XGroup g) {
        JUniverseAceProblemAdapter.inGroup=false;
    }
    
    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildVarInteger(org.xcsp.parser.entries.
     * XVariables.XVarInteger, int, int)
     */
    @Override
    public void buildVarInteger(XVarInteger x, int minValue, int maxValue) {
        listener.newVariable(x.id(), minValue, maxValue);
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildVarInteger(org.xcsp.parser.entries.
     * XVariables.XVarInteger, int[])
     */
    @Override
    public void buildVarInteger(XVarInteger x, int[] values) {
        listener.newVariable(x.id(), Arrays.stream(values).boxed().collect(Collectors.toList()));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrClause(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrClause(String id, XVarInteger[] pos, XVarInteger[] neg) {
       
            listener.addClause(toVariableIdentifiers(pos), toVariableIdentifiers(neg));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLogic(java.lang.String,
     * org.xcsp.common.Types.TypeLogicalOperator,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrLogic(String id, TypeLogicalOperator op, XVarInteger[] vars) {
        
            listener.addLogical(TYPE_LOGIC_OP_TO_BOOL_OP.get(op), toVariableIdentifiers(vars));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLogic(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeEqNeOperator, org.xcsp.common.Types.TypeLogicalOperator,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrLogic(String id, XVarInteger x, TypeEqNeOperator op,
            TypeLogicalOperator lop, XVarInteger[] vars) {

            listener.addLogical(x.id(), op == TypeEqNeOperator.EQ,
                    TYPE_LOGIC_OP_TO_BOOL_OP.get(lop), toVariableIdentifiers(vars));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLogic(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorRel, int)
     */
    @Override
    public void buildCtrLogic(String id, XVarInteger x, XVarInteger y,
            TypeConditionOperatorRel op, int k) {

            listener.addLogical(x.id(),
                    y.id(), TYPE_COND_OP_REL_TO_REL_OP.get(op), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLogic(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorRel,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrLogic(String id, XVarInteger x, XVarInteger y,
            TypeConditionOperatorRel op, XVarInteger z) {

            listener.addLogical(x.id(),
                    y.id(), TYPE_COND_OP_REL_TO_REL_OP.get(op), z.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferent(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrAllDifferent(String id, XVarInteger[] list) {

            listener.addAllDifferent(toVariableIdentifiers(list));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferentExcept(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[])
     */
    @Override
    public void buildCtrAllDifferentExcept(String id, XVarInteger[] list, int[] except) {

            listener.addAllDifferent(toVariableIdentifiers(list), toBigInteger(except));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferentList(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][])
     */
    @Override
    public void buildCtrAllDifferentList(String id, XVarInteger[][] lists) {

            listener.addAllDifferentList(toVariableIdentifiers(lists));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferentMatrix(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][])
     */
    @Override
    public void buildCtrAllDifferentMatrix(String id, XVarInteger[][] matrix) {

            listener.addAllDifferentMatrix(toVariableIdentifiers(matrix));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferentMatrix(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][], int[])
     */
    @Override
    public void buildCtrAllDifferentMatrix(String id, XVarInteger[][] matrix, int[] except) {

            listener.addAllDifferentMatrix(toVariableIdentifiers(matrix), toBigInteger(except));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllDifferent(java.lang.String,
     * org.xcsp.common.predicates.XNode[])
     */
    @Override
    public void buildCtrAllDifferent(String id, XNode<XVarInteger>[] trees) {

            listener.addAllDifferentIntension(toIntensionConstraints(trees));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllEqual(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrAllEqual(String id, XVarInteger[] list) {

            listener.addAllEqual(toVariableIdentifiers(list));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAllEqual(java.lang.String,
     * org.xcsp.common.predicates.XNode[])
     */
    @Override
    public void buildCtrAllEqual(String id, XNode<XVarInteger>[] trees) {

            listener.addAllEqualIntension(toIntensionConstraints(trees));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNotAllEqual(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrNotAllEqual(String id, XVarInteger[] list) {

            listener.addNotAllEqual(toVariableIdentifiers(list));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAmong(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], int)
     */
    @Override
    public void buildCtrAmong(String id, XVarInteger[] list, int[] values, int k) {

            listener.addAmong(
                    toVariableIdentifiers(list), toBigInteger(values), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAmong(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[],
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrAmong(String id, XVarInteger[] list, int[] values, XVarInteger k) {

            listener.addAmong(toVariableIdentifiers(list), toBigInteger(values), k.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAtLeast(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int, int)
     */
    @Override
    public void buildCtrAtLeast(String id, XVarInteger[] list, int value, int k) {

            listener.addAtLeast(
                    toVariableIdentifiers(list), BigInteger.valueOf(value), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrAtMost(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int, int)
     */
    @Override
    public void buildCtrAtMost(String id, XVarInteger[] list, int value, int k) {

            listener.addAtMost(
                    toVariableIdentifiers(list), BigInteger.valueOf(value), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean, int[], int[], int[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values,
            int[] occursMin, int[] occursMax) {

            listener.addCardinalityWithConstantValuesAndConstantIntervalCounts(
                    toVariableIdentifiers(list), toBigInteger(values), toBigInteger(occursMin),
                    toBigInteger(occursMax), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean, int[], int[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values,
            int[] occurs) {

            listener.addCardinalityWithConstantValuesAndConstantCounts(toVariableIdentifiers(list),
                    toBigInteger(values), toBigInteger(occurs), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean, int[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed, int[] values,
            XVarInteger[] occurs) {

            listener.addCardinalityWithConstantValuesAndVariableCounts(
                    toVariableIdentifiers(list), toBigInteger(values),
                    toVariableIdentifiers(occurs), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], int[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed,
            XVarInteger[] values, int[] occursMin, int[] occursMax) {

            listener.addCardinalityWithVariableValuesAndConstantIntervalCounts(
                    toVariableIdentifiers(list), toVariableIdentifiers(values),
                    toBigInteger(occursMin), toBigInteger(occursMax), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed,
            XVarInteger[] values, int[] occurs) {

            listener.addCardinalityWithVariableValuesAndConstantCounts(
                    toVariableIdentifiers(list), toVariableIdentifiers(values),
                    toBigInteger(occurs), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCardinality(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildCtrCardinality(String id, XVarInteger[] list, boolean closed,
            XVarInteger[] values, XVarInteger[] occurs) {

            listener.addCardinalityWithVariableValuesAndVariableCounts(
                    toVariableIdentifiers(list), toVariableIdentifiers(values),
                    toVariableIdentifiers(occurs), closed);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrChannel(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrChannel(String id, XVarInteger[] list, int startIndex, XVarInteger value) {

            listener.addChannel(toVariableIdentifiers(list), startIndex, value.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrChannel(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int)
     */
    @Override
    public void buildCtrChannel(String id, XVarInteger[] list1, int startIndex1,
            XVarInteger[] list2, int startIndex2) {

            listener.addChannel(toVariableIdentifiers(list1), startIndex1,
                    toVariableIdentifiers(list2), startIndex2);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrChannel(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int)
     */
    @Override
    public void buildCtrChannel(String id, XVarInteger[] list, int startIndex) {

            listener.addChannel(toVariableIdentifiers(list), startIndex);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCount(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCount(String id, XVarInteger[] list, int[] values, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCountWithConstantValues(toVariableIdentifiers(list),
                        toBigInteger(values), op, rhs),
                (op, rhs) -> listener.addCountWithConstantValues(toVariableIdentifiers(list),
                        toBigInteger(values), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCount(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCount(String id, XVarInteger[] list, XVarInteger[] values,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCountWithVariableValues(toVariableIdentifiers(list),
                        toVariableIdentifiers(values), op, rhs),
                (op, rhs) -> listener.addCountWithVariableValues(toVariableIdentifiers(list),
                        toVariableIdentifiers(values), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCount(java.lang.String,
     * org.xcsp.common.predicates.XNode[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCount(String id, XNode<XVarInteger>[] trees, int[] values,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCountIntensionWithConstantValues(
                        toIntensionConstraints(trees), toBigInteger(values), op, rhs),
                (op, rhs) -> listener.addCountIntensionWithConstantValues(
                        toIntensionConstraints(trees), toBigInteger(values), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], int[],
     * org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths, int[] heights,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeConstantLengthsConstantHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toBigInteger(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeConstantLengthsConstantHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toBigInteger(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths,
            XVarInteger[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeConstantLengthsVariableHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeConstantLengthsVariableHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths,
            XVarInteger[] ends, int[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeConstantLengthsConstantHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(ends), toBigInteger(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeConstantLengthsConstantHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(ends), toBigInteger(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, int[] lengths,
            XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeConstantLengthsVariableHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(ends), toVariableIdentifiers(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeConstantLengthsVariableHeights(
                        toVariableIdentifiers(origins), toBigInteger(lengths),
                        toVariableIdentifiers(ends), toVariableIdentifiers(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths,
            int[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeVariableLengthsConstantHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toBigInteger(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeVariableLengthsConstantHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toBigInteger(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths,
            XVarInteger[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeVariableLengthsVariableHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeVariableLengthsVariableHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths,
            XVarInteger[] ends, int[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeVariableLengthsConstantHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(ends), toBigInteger(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeVariableLengthsConstantHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(ends), toBigInteger(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrCumulative(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrCumulative(String id, XVarInteger[] origins, XVarInteger[] lengths,
            XVarInteger[] ends, XVarInteger[] heights, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addCumulativeVariableLengthsVariableHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(ends), toVariableIdentifiers(heights), op, rhs),
                (op, rhs) -> listener.addCumulativeVariableLengthsVariableHeights(
                        toVariableIdentifiers(origins), toVariableIdentifiers(lengths),
                        toVariableIdentifiers(ends), toVariableIdentifiers(heights), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrElement(java.lang.String,
     * int[][], int, org.xcsp.parser.entries.XVariables.XVarInteger, int,
     * org.xcsp.parser.entries.XVariables.XVarInteger, int)
     */
    @Override
    public void buildCtrElement(String id, int[][] matrix, int startRowIndex, XVarInteger rowIndex,
            int startColIndex, XVarInteger colIndex, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addElementConstantMatrix(
                        toBigInteger(matrix), startRowIndex, rowIndex.id(), startColIndex,
                        colIndex.id(), rhs),
                (op, rhs) -> listener.addElementConstantMatrix(
                        toBigInteger(matrix), startRowIndex, rowIndex.id(), startColIndex,
                        colIndex.id(), rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrElement(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int)
     */
    @Override
    public void buildCtrElement(String id, XVarInteger[] list, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addElement(toVariableIdentifiers(list), rhs),
                (op, rhs) -> listener.addElement(toVariableIdentifiers(list), rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrElement(java.lang.String, int[],
     * int, org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeRank, org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrElement(String id, int[] list, int startIndex, XVarInteger index,
            TypeRank rank, Condition condition) {
        if (rank != TypeRank.ANY) {
            throw new UnsupportedOperationException("Unsupported type rank for element: " + rank);
        }

        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addElementConstantValues(
                        toBigInteger(list), startIndex, index.id(), rhs),
                (op, rhs) -> listener.addElementConstantValues(
                        toBigInteger(list), startIndex, index.id(), rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrElement(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int,
     * org.xcsp.parser.entries.XVariables.XVarInteger, org.xcsp.common.Types.TypeRank,
     * int)
     */
    @Override
    public void buildCtrElement(String id, XVarInteger[] list, int startIndex, XVarInteger index,
            TypeRank rank, Condition condition) {
        if (rank != TypeRank.ANY) {
            throw new UnsupportedOperationException("Unsupported type rank for element: " + rank);
        }

        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addElement(
                        toVariableIdentifiers(list), startIndex, index.id(), rhs),
                (op, rhs) -> listener.addElement(
                        toVariableIdentifiers(list), startIndex, index.id(), rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrElement(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][], int,
     * org.xcsp.parser.entries.XVariables.XVarInteger, int,
     * org.xcsp.parser.entries.XVariables.XVarInteger, int)
     */
    @Override
    public void buildCtrElement(String id, XVarInteger[][] matrix, int startRowIndex,
            XVarInteger rowIndex, int startColIndex, XVarInteger colIndex, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addElementMatrix(
                        toVariableIdentifiers(matrix), startRowIndex, rowIndex.id(), startColIndex,
                        colIndex.id(), rhs),
                (op, rhs) -> listener.addElementMatrix(
                        toVariableIdentifiers(matrix), startRowIndex, rowIndex.id(), startColIndex,
                        colIndex.id(), rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrExactly(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int, int)
     */
    @Override
    public void buildCtrExactly(String id, XVarInteger[] list, int value, int k) {

            listener.addExactly(
                    toVariableIdentifiers(list), BigInteger.valueOf(value), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrExactly(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrExactly(String id, XVarInteger[] list, int value, XVarInteger k) {

            listener.addExactly(toVariableIdentifiers(list), BigInteger.valueOf(value), k.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrExtension(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger, int[], boolean, java.util.Set)
     */
    @Override
    public void buildCtrExtension(String id, XVarInteger x, int[] values, boolean positive,
            Set<TypeFlag> flags) {

            if (positive) {
                listener.addSupport(x.id(), toBigInteger(values));
            } else {
                listener.addConflicts(x.id(), toBigInteger(values));
            }

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrExtension(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[][], boolean, java.util.Set)
     */
    @Override
    public void buildCtrExtension(String id, XVarInteger[] list, int[][] tuples, boolean positive,
            Set<TypeFlag> flags) {

            if (positive) {
                listener.addSupport(toVariableIdentifiers(list),
                        toBigInteger(tuples, flags.contains(TypeFlag.STARRED_TUPLES)));
            } else {
                listener.addConflicts(toVariableIdentifiers(list),
                        toBigInteger(tuples, flags.contains(TypeFlag.STARRED_TUPLES)));
            }

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrInstantiation(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[])
     */
    @Override
    public void buildCtrInstantiation(String id, XVarInteger[] list, int[] values) {

            listener.addInstantiation(toVariableIdentifiers(list), toBigInteger(values));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrIntension(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.common.predicates.XNodeParent)
     */
    @Override
    public void buildCtrIntension(String id, XVarInteger[] scope, XNodeParent<XVarInteger> tree) {

            listener.addIntension(new IntensionConstraintXNodeAdapter(tree));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLex(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][],
     * org.xcsp.common.Types.TypeOperatorRel)
     */
    @Override
    public void buildCtrLex(String id, XVarInteger[][] lists, TypeOperatorRel operator) {

            listener.addLex(toVariableIdentifiers(lists), TYPE_OP_REL_TO_REL_OP.get(operator));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrLexMatrix(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][],
     * org.xcsp.common.Types.TypeOperatorRel)
     */
    @Override
    public void buildCtrLexMatrix(String id, XVarInteger[][] matrix, TypeOperatorRel operator) {

            listener.addLexMatrix(
                    toVariableIdentifiers(matrix), TYPE_OP_REL_TO_REL_OP.get(operator));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrMaximum(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrMaximum(String id, XVarInteger[] list, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addMaximum(toVariableIdentifiers(list), op, rhs),
                (op, rhs) -> listener.addMaximum(toVariableIdentifiers(list), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrMaximum(java.lang.String,
     * org.xcsp.common.predicates.XNode[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrMaximum(String id, XNode<XVarInteger>[] trees, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addMaximumIntension(toIntensionConstraints(trees), op, rhs),
                (op, rhs) -> listener.addMaximumIntension(toIntensionConstraints(trees), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrMinimum(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrMinimum(String id, XVarInteger[] list, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addMinimum(toVariableIdentifiers(list), op, rhs),
                (op, rhs) -> listener.addMinimum(toVariableIdentifiers(list), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrMinimum(java.lang.String,
     * org.xcsp.common.predicates.XNode[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrMinimum(String id, XNode<XVarInteger>[] trees, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addMinimumIntension(toIntensionConstraints(trees), op, rhs),
                (op, rhs) -> listener.addMinimumIntension(toIntensionConstraints(trees), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNValues(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrNValues(String id, XVarInteger[] list, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addNValues(toVariableIdentifiers(list), op, rhs),
                (op, rhs) -> listener.addNValues(toVariableIdentifiers(list), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNValuesExcept(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrNValuesExcept(String id, XVarInteger[] list, int[] except,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addNValuesExcept(
                        toVariableIdentifiers(list), op, rhs, toBigInteger(except)),
                (op, rhs) -> listener.addNValuesExcept(
                        toVariableIdentifiers(list), op, rhs, toBigInteger(except)));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNValues(java.lang.String,
     * org.xcsp.common.predicates.XNode[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrNValues(String id, XNode<XVarInteger>[] trees, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addNValuesIntension(toIntensionConstraints(trees), op, rhs),
                (op, rhs) -> listener.addNValuesIntension(toIntensionConstraints(trees), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNoOverlap(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], boolean)
     */
    @Override
    public void buildCtrNoOverlap(String id, XVarInteger[] origins, int[] lengths,
            boolean zeroIgnored) {

            listener.addNoOverlap(
                    toVariableIdentifiers(origins), toBigInteger(lengths), zeroIgnored);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNoOverlap(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], boolean)
     */
    @Override
    public void buildCtrNoOverlap(String id, XVarInteger[] origins, XVarInteger[] lengths,
            boolean zeroIgnored) {

            listener.addNoOverlapVariableLength(
                    toVariableIdentifiers(origins), toVariableIdentifiers(lengths), zeroIgnored);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNoOverlap(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][], int[][], boolean)
     */
    @Override
    public void buildCtrNoOverlap(String id, XVarInteger[][] origins, int[][] lengths,
            boolean zeroIgnored) {

            listener.addMultiDimensionalNoOverlap(
                    toVariableIdentifiers(origins), toBigInteger(lengths), zeroIgnored);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrNoOverlap(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[][],
     * org.xcsp.parser.entries.XVariables.XVarInteger[][], boolean)
     */
    @Override
    public void buildCtrNoOverlap(String id, XVarInteger[][] origins, XVarInteger[][] lengths,
            boolean zeroIgnored) {

            listener.addMultiDimensionalNoOverlapVariableLength(
                    toVariableIdentifiers(origins), toVariableIdentifiers(lengths), zeroIgnored);

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrOrdered(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[],
     * org.xcsp.common.Types.TypeOperatorRel)
     */
    @Override
    public void buildCtrOrdered(String id, XVarInteger[] list, int[] lengths,
            TypeOperatorRel operator) {
            listener.addOrderedWithConstantLength(toVariableIdentifiers(list),
                    toBigInteger(lengths), TYPE_OP_REL_TO_REL_OP.get(operator));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrOrdered(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.common.Types.TypeOperatorRel)
     */
    @Override
    public void buildCtrOrdered(String id, XVarInteger[] list, TypeOperatorRel operator) {

            listener.addOrdered(toVariableIdentifiers(list), TYPE_OP_REL_TO_REL_OP.get(operator));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrOrdered(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.common.Types.TypeOperatorRel)
     */
    @Override
    public void buildCtrOrdered(String id, XVarInteger[] list, XVarInteger[] lengths,
            TypeOperatorRel operator) {

            listener.addOrderedWithVariableLength(toVariableIdentifiers(list),
                    toVariableIdentifiers(lengths), TYPE_OP_REL_TO_REL_OP.get(operator));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorRel, int)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorRel op, int k) {

            listener.addPrimitive(
                    x.id(), TYPE_COND_OP_REL_TO_REL_OP.get(op), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeArithmeticOperator, int,
     * org.xcsp.common.Types.TypeConditionOperatorRel, int)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int p,
            TypeConditionOperatorRel op, int k) {

            listener.addPrimitive(x.id(), TYPE_ARITH_OP_TO_ARITH_OP.get(aop), BigInteger.valueOf(p),
                    TYPE_COND_OP_REL_TO_REL_OP.get(op), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeArithmeticOperator, int,
     * org.xcsp.common.Types.TypeConditionOperatorRel,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop, int p,
            TypeConditionOperatorRel op, XVarInteger y) {
            listener.addPrimitive(x.id(), TYPE_ARITH_OP_TO_ARITH_OP.get(aop), BigInteger.valueOf(p),
                    TYPE_COND_OP_REL_TO_REL_OP.get(op), y.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeArithmeticOperator,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorRel, int)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop,
            XVarInteger y, TypeConditionOperatorRel op, int k) {
            listener.addPrimitive(x.id(), TYPE_ARITH_OP_TO_ARITH_OP.get(aop), y.id(),
                    TYPE_COND_OP_REL_TO_REL_OP.get(op), BigInteger.valueOf(k));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeArithmeticOperator,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorRel,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeArithmeticOperator aop,
            XVarInteger y, TypeConditionOperatorRel op, XVarInteger z) {

            listener.addPrimitive(x.id(), TYPE_ARITH_OP_TO_ARITH_OP.get(aop), y.id(),
                    TYPE_COND_OP_REL_TO_REL_OP.get(op), z.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeUnaryArithmeticOperator,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeUnaryArithmeticOperator aop,
            XVarInteger y) {

            listener.addPrimitive(TYPE_UNARY_ARITH_OP_TO_ARITH_OP.get(aop), y.id(), x.id());

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorSet, int[])
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op, int[] t) {

            listener.addPrimitive(x.id(), TYPE_COND_OP_SET_TO_SET_OP.get(op), toBigInteger(t));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrPrimitive(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger,
     * org.xcsp.common.Types.TypeConditionOperatorSet, int, int)
     */
    @Override
    public void buildCtrPrimitive(String id, XVarInteger x, TypeConditionOperatorSet op,
            int min, int max) {

            listener.addPrimitive(x.id(), TYPE_COND_OP_SET_TO_SET_OP.get(op),
                    BigInteger.valueOf(min), BigInteger.valueOf(max));

    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XVarInteger[] list, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSum(toVariableIdentifiers(list), op, rhs),
                (op, rhs) -> listener.addSum(toVariableIdentifiers(list), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XVarInteger[] list, int[] coeffs, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSum(
                        toVariableIdentifiers(list), toBigInteger(coeffs), op, rhs),
                (op, rhs) -> listener.addSum(
                        toVariableIdentifiers(list), toBigInteger(coeffs), op, rhs),
                (op, rhs) -> listener.addSum(
                        toVariableIdentifiers(list), toBigInteger(coeffs), op, rhs[0],rhs[1]),
                (op, rhs) -> listener.addSum(
                        toVariableIdentifiers(list), toBigInteger(coeffs), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.common.predicates.XNode[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XNode<XVarInteger>[] trees, Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSumIntension(toIntensionConstraints(trees), op, rhs),
                (op, rhs) -> listener.addSumIntension(toIntensionConstraints(trees), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.common.predicates.XNode[], int[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XNode<XVarInteger>[] trees, int[] coeffs,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSumIntension(
                        toIntensionConstraints(trees), toBigInteger(coeffs), op, rhs),
                (op, rhs) -> listener.addSumIntension(
                        toIntensionConstraints(trees), toBigInteger(coeffs), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XVarInteger[] list, XVarInteger[] coeffs,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSumWithVariableCoefficients(
                        toVariableIdentifiers(list), toVariableIdentifiers(coeffs), op, rhs),
                (op, rhs) -> listener.addSumWithVariableCoefficients(
                        toVariableIdentifiers(list), toVariableIdentifiers(coeffs), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildCtrSum(java.lang.String,
     * org.xcsp.common.predicates.XNode[],
     * org.xcsp.parser.entries.XVariables.XVarInteger[], org.xcsp.common.Condition)
     */
    @Override
    public void buildCtrSum(String id, XNode<XVarInteger>[] trees, XVarInteger[] coeffs,
            Condition condition) {
        buildCtrWithCondition(condition,
                (op, rhs) -> listener.addSumIntensionWithVariableCoefficients(
                        toIntensionConstraints(trees), toVariableIdentifiers(coeffs), op, rhs),
                (op, rhs) -> listener.addSumIntensionWithVariableCoefficients(
                        toIntensionConstraints(trees), toVariableIdentifiers(coeffs), op, rhs));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildObjToMinimize(String id, XVarInteger x) {
        listener.minimizeVariable(x.id());
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.parser.entries.XVariables.XVarInteger)
     */
    @Override
    public void buildObjToMaximize(String id, XVarInteger x) {
        listener.maximizeVariable(x.id());
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.common.predicates.XNodeParent)
     */
    @Override
    public void buildObjToMinimize(String id, XNodeParent<XVarInteger> tree) {
        listener.minimizeExpression(new IntensionConstraintXNodeAdapter(tree));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.common.predicates.XNodeParent)
     */
    @Override
    public void buildObjToMaximize(String id, XNodeParent<XVarInteger> tree) {
        listener.maximizeExpression(new IntensionConstraintXNodeAdapter(tree));
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildObjToMinimize(String id, TypeObjective type, XVarInteger[] list) {
        if (type == TypeObjective.SUM) {
            listener.minimizeSum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.PRODUCT) {
            listener.minimizeProduct(toVariableIdentifiers(list));

        } else if (type == TypeObjective.MINIMUM) {
            listener.minimizeMinimum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.minimizeMaximum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.NVALUES) {
            listener.minimizeNValues(toVariableIdentifiers(list));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective,
     * org.xcsp.parser.entries.XVariables.XVarInteger[])
     */
    @Override
    public void buildObjToMaximize(String id, TypeObjective type, XVarInteger[] list) {
        if (type == TypeObjective.SUM) {
            listener.maximizeSum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.PRODUCT) {
            listener.maximizeProduct(toVariableIdentifiers(list));

        } else if (type == TypeObjective.MINIMUM) {
            listener.maximizeMinimum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.maximizeMaximum(toVariableIdentifiers(list));

        } else if (type == TypeObjective.NVALUES) {
            listener.maximizeNValues(toVariableIdentifiers(list));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[])
     */
    @Override
    public void buildObjToMinimize(String id, TypeObjective type, XVarInteger[] list,
            int[] coeffs) {
        if (type == TypeObjective.SUM) {
            listener.minimizeSum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.PRODUCT) {
            listener.minimizeProduct(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.MINIMUM) {
            listener.minimizeMinimum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.minimizeMaximum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.NVALUES) {
            listener.minimizeNValues(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective,
     * org.xcsp.parser.entries.XVariables.XVarInteger[], int[])
     */
    @Override
    public void buildObjToMaximize(String id, TypeObjective type, XVarInteger[] list,
            int[] coeffs) {
        if (type == TypeObjective.SUM) {
            listener.maximizeSum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.PRODUCT) {
            listener.maximizeProduct(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.MINIMUM) {
            listener.maximizeMinimum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.maximizeMaximum(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else if (type == TypeObjective.NVALUES) {
            listener.maximizeNValues(toVariableIdentifiers(list), toBigInteger(coeffs));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective, org.xcsp.common.predicates.XNode[])
     */
    @Override
    public void buildObjToMinimize(String id, TypeObjective type, XNode<XVarInteger>[] trees) {
        if (type == TypeObjective.SUM) {
            listener.minimizeExpressionSum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.PRODUCT) {
            listener.minimizeExpressionProduct(toIntensionConstraints(trees));

        } else if (type == TypeObjective.MINIMUM) {
            listener.minimizeExpressionMinimum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.minimizeExpressionMaximum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.NVALUES) {
            listener.minimizeExpressionNValues(toIntensionConstraints(trees));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective, org.xcsp.common.predicates.XNode[])
     */
    @Override
    public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees) {
        if (type == TypeObjective.SUM) {
            listener.maximizeExpressionSum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.PRODUCT) {
            listener.maximizeExpressionProduct(toIntensionConstraints(trees));

        } else if (type == TypeObjective.MINIMUM) {
            listener.maximizeExpressionMinimum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.maximizeExpressionMaximum(toIntensionConstraints(trees));

        } else if (type == TypeObjective.NVALUES) {
            listener.maximizeExpressionNValues(toIntensionConstraints(trees));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMinimize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective, org.xcsp.common.predicates.XNode[], int[])
     */
    @Override
    public void buildObjToMinimize(String id, TypeObjective type, XNode<XVarInteger>[] trees,
            int[] coeffs) {
        if (type == TypeObjective.SUM) {
            listener.minimizeExpressionSum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.PRODUCT) {
            listener.minimizeExpressionProduct(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.MINIMUM) {
            listener.minimizeExpressionMinimum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.minimizeExpressionMaximum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.NVALUES) {
            listener.minimizeExpressionNValues(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see org.xcsp.parser.callbacks.XCallbacks2#buildObjToMaximize(java.lang.String,
     * org.xcsp.common.Types.TypeObjective, org.xcsp.common.predicates.XNode[], int[])
     */
    @Override
    public void buildObjToMaximize(String id, TypeObjective type, XNode<XVarInteger>[] trees,
            int[] coeffs) {
        if (type == TypeObjective.SUM) {
            listener.maximizeExpressionSum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.PRODUCT) {
            listener.maximizeExpressionProduct(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.MINIMUM) {
            listener.maximizeExpressionMinimum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.MAXIMUM) {
            listener.maximizeExpressionMaximum(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else if (type == TypeObjective.NVALUES) {
            listener.maximizeExpressionNValues(toIntensionConstraints(trees), toBigInteger(coeffs));

        } else {
            throw new UnsupportedOperationException(
                    "Objective function of type " + type + " is not (yet?) supported");
        }
    }
    @Override
    public void buildAnnotationDecision(XVarInteger[] list) {
    	listener.decisionVariables(toVariableIdentifiers(list));
    }
    /**
     * Transforms an array of {@code int} values into a vector of {@link BigInteger}.
     *
     * @param array The array to transform.
     *
     * @return The vector of {@link BigInteger}.
     */
    private static List<BigInteger> toBigInteger(int[] array) {
        return toBigInteger(array, false);
    }

    /**
     * Transforms an array of {@code int} values into a vector of {@link BigInteger}.
     *
     * @param array The array to transform
     * @param starred Whether {@link Constants#STAR_INT} must be interpreted as a
     *        {@code *}.
     *
     * @return The vector of {@link BigInteger}.
     */
    private static List<BigInteger> toBigInteger(int[] array, boolean starred) {
        var vec = new ArrayList<BigInteger>(array.length);
        for (var i : array) {
            if (starred && (i == Constants.STAR_INT)) {
                vec.add(null);

            } else {
                vec.add(BigInteger.valueOf(i));
            }
        }
        return vec;
    }

    /**
     * Transforms a matrix of {@code int} values into a vector-based matrix of
     * {@link BigInteger}.
     *
     * @param matrix The matrix to transform.
     *
     * @return The matrix of {@link BigInteger}.
     */
    private static List<List<BigInteger>> toBigInteger(int[][] matrix) {
        return toBigInteger(matrix, false);
    }

    /**
     * Transforms a matrix of {@code int} values into a vector-based matrix of
     * {@link BigInteger}.
     *
     * @param matrix The matrix to transform.
     * @param starred Whether {@link Constants#STAR_INT} must be interpreted as a
     *        {@code *}.
     *
     * @return The matrix of {@link BigInteger}.
     */
    private static List<List<BigInteger>> toBigInteger(int[][] matrix, boolean starred) {
        var vec = new ArrayList<List<BigInteger>>(matrix.length);
        for (var array : matrix) {
            vec.add(toBigInteger(array, starred));
        }
        return vec;
    }

    /**
     * Extracts the identifiers of the given variables.
     *
     * @param array The array of the variables to extract the identifiers of.
     *
     * @return The vector of the identifiers of the variables in the array.
     */
    private static List<String> toVariableIdentifiers(XVarInteger[] array) {
        var vec = new ArrayList<String>(array.length);
        for (var v : array) {
            vec.add(v.id());
        }
        return vec;
    }

    /**
     * Extracts the identifiers of the given variables.
     *
     * @param matrix The matrix of the variables to extract the identifiers of.
     *
     * @return The matrix of the identifiers of the variables in the matrix.
     */
    private static List<List<String>> toVariableIdentifiers(XVarInteger[][] matrix) {
    	List<List<String>> vec = new ArrayList<List<String>>(matrix.length);
        for (var array : matrix) {
            vec.add(toVariableIdentifiers(array));
        }
        return vec;
    }

    /**
     * Adapts an array of {@link XNode} to a vector of intension constraints.
     *
     * @param nodes The nodes to adapt.
     *
     * @return The vector of intension constraints.
     */
    private static List<IIntensionConstraint> toIntensionConstraints(XNode<?>[] nodes) {
        var vec = new ArrayList<IIntensionConstraint>(nodes.length);
        for (var n : nodes) {
            vec.add(new IntensionConstraintXNodeAdapter(n));
        }
        return vec;
    }

    /**
     * The ConditionalConstraintBuilder is a private functional interface allowing to deal
     * with {@link Condition} objects, and especially to invoke the right method depending
     * on the type of the right-hand side of this {@link Condition} using lambda
     * expressions to avoid code duplication.
     *
     * This interface is only intended to be used by {@link XCSPXCallback} instances,
     * hence its private status within this class.
     *
     * @param <O> The type of the operator used in the constraint.
     * @param <T> The type of the value of the right-hand side of the constraint.
     */
    @FunctionalInterface
    private static interface ConditionalConstraintBuilder<O extends UniverseOperator, T> {

        /**
         * Builds the constraint based on a {@link Condition} object.
         *
         * @param operator The operator of the condition.
         * @param rightHandSide The right-hand side of the condition.
         *
         * @throws UniverseContradictionException If building the constraint results in a trivial
         *         inconsistency.
         */
        void buildCtr(O operator, T rightHandSide);

    }

    /**
     * Builds a constraint that uses a condition.
     * The type of the right-hand side of the constraint will be used to choose the right
     * way of building the constraint.
     *
     * @param condition The condition of the constraint to build.
     * @param ifConstant The builder to use to build a constraint if the condition has a
     *        constant on its right-hand side.
     * @param ifVariable The builder to use to build a constraint if the condition has a
     *        variable on its right-hand side.
     *
     * @throws UnsupportedOperationException If the condition uses an unrecognized
     *         operator for the constraint to build.
     */
    private void buildCtrWithCondition(Condition condition,
            ConditionalConstraintBuilder<UniverseRelationalOperator, BigInteger> ifConstant,
            ConditionalConstraintBuilder<UniverseRelationalOperator, String> ifVariable) {
        buildCtrWithCondition(condition, ifConstant, ifVariable,
                (op, rhs) -> {
                    throw new UnsupportedOperationException(
                            "Sets are not supported (yet?) for this constraint");
                },
                (op, rhs) -> {
                    throw new UnsupportedOperationException(
                            "Sets are not supported (yet?) for this constraint");
                });
    }

    /**
     * Builds a constraint that uses a condition.
     * The type of the right-hand side of the constraint will be used to choose the right
     * way of building the constraint.
     *
     * @param condition The condition of the constraint to build.
     * @param ifConstant The builder to use to build a constraint if the condition has a
     *        constant on its right-hand side.
     * @param ifVariable The builder to use to build a constraint if the condition has a
     *        variable on its right-hand side.
     * @param ifRange The builder to use to build a constraint if the condition has a
     *        range on its right-hand side.
     * @param ifSetOfValues The builder to use to build a constraint if the condition has
     *        a set on its right-hand side.
     *
     * @throws UnsupportedOperationException If the condition uses an unrecognized
     *         operator.
     */
    private void buildCtrWithCondition(Condition condition,
            ConditionalConstraintBuilder<UniverseRelationalOperator, BigInteger> ifConstant,
            ConditionalConstraintBuilder<UniverseRelationalOperator, String> ifVariable,
            ConditionalConstraintBuilder<UniverseSetBelongingOperator, BigInteger[]> ifRange,
            ConditionalConstraintBuilder<UniverseSetBelongingOperator, List<BigInteger>> ifSetOfValues) {

            // Getting the operator involved in the condition.
            var operator = condition.operatorTypeExpr();

            // Considering the case where the condition uses a relational operator.
            if (operator.isRelationalOperator()) {
                buildCtrRelational(condition, ifConstant, ifVariable);
                return;
            }

            // Considering the case where the condition is on a set.
            if ((operator == TypeExpr.IN) || (operator == TypeExpr.NOTIN)) {
                buildCtrConditionSet(condition, ifRange, ifSetOfValues);
                return;
            }

            throw new UnsupportedOperationException(
                    "Unknown condition operator: " + operator);


    }

    /**
     * Builds a constraint that uses a relational-based condition.
     * The type of the right-hand side of the constraint will be used to choose the right
     * way of building the constraint.
     *
     * @param condition The condition of the constraint to build.
     * @param ifConstant The builder to use to build a constraint if the condition has a
     *        constant on its right-hand side.
     * @param ifVariable The builder to use to build a constraint if the condition has a
     *        variable on its right-hand side.
     *
     * @throws UniverseContradictionException If building the constraint results in a trivial
     *         inconsistency.
     * @throws UnsupportedOperationException If the condition uses an unrecognized
     *         operator.
     */
    private void buildCtrRelational(Condition condition,
            ConditionalConstraintBuilder<UniverseRelationalOperator, BigInteger> ifConstant,
            ConditionalConstraintBuilder<UniverseRelationalOperator, String> ifVariable)
             {
        // Translating the operator to the appropriate type.
        var relOperator = TYPE_EXPR_TO_REL_OP.get(condition.operatorTypeExpr());

        // Checking whether the condition involves a variable.
        var variable = condition.involvedVar();
        if (variable == null) {
            // The right-hand side is a value.
            ifConstant.buildCtr(relOperator, BigInteger.valueOf((long) condition.rightTerm()));

        } else {
            // The right-hand side is a variable.
            ifVariable.buildCtr(relOperator, variable.id());
        }
    }

    /**
     * Builds a constraint that uses a set-based condition.
     * The type of the right-hand side of the constraint will be used to choose the right
     * way of building the constraint.
     *
     * @param condition The condition of the constraint to build.
     * @param ifRange The builder to use to build a constraint if the condition has a
     *        range on its right-hand side.
     * @param ifSetOfValues The builder to use to build a constraint if the condition has
     *        a set on its right-hand side.
     *
     * @throws UniverseContradictionException If building the constraint results in a trivial
     *         inconsistency.
     * @throws UnsupportedOperationException If the condition uses an unrecognized
     *         operator.
     */
    private void buildCtrConditionSet(Condition condition,
            ConditionalConstraintBuilder<UniverseSetBelongingOperator, BigInteger[]> ifRange,
            ConditionalConstraintBuilder<UniverseSetBelongingOperator, List<BigInteger>> ifSetOfValues)
            throws UniverseContradictionException {
        // Translating the operator to the appropriate type.
        var setOperator = UniverseSetBelongingOperator.IN;
        if (condition.operatorTypeExpr() == TypeExpr.NOTIN) {
            setOperator = UniverseSetBelongingOperator.NOT_IN;
        }

        if (condition instanceof ConditionIntvl) {
            // The set is represented with a range.
            var range = (ConditionIntvl) condition;
            var min = BigInteger.valueOf(range.min);
            var max = BigInteger.valueOf(range.max);
            ifRange.buildCtr(setOperator, new BigInteger[] { min, max });
            return;
        }

        if (condition instanceof ConditionIntset) {
            // The set is represented with an array of values.
            var set = (ConditionIntset) condition;
            ifSetOfValues.buildCtr(setOperator, toBigInteger(set.t));
            return;
        }

        throw new UnsupportedOperationException(
                "Unknown condition type: " + condition.getClass());
    }

}
