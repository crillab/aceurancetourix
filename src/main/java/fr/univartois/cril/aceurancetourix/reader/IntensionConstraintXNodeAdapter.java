/**
 * Sat4j-CSP, a CSP solver based on the Sat4j platform.
 * Copyright (c) 2021-2022 - Thibault Falque and Romain Wallon.
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

import static java.util.stream.Collectors.toList;

import java.math.BigInteger;
import java.util.Map;
import java.util.stream.Stream;

import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;

import fr.univartois.cril.juniverse.core.UniverseContradictionException;
import fr.univartois.cril.juniverse.csp.intension.BinaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.ConstantIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.IIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor;
import fr.univartois.cril.juniverse.csp.intension.IfThenElseIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.NaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UnaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.VariableIntensionConstraint;
import fr.univartois.cril.juniverse.csp.operator.UniverseArithmeticOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseBooleanOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator;

/**
 * The IntensionConstraintXNodeAdapter is a (lazy) adapter for an {@link XNode}
 * representation of an {@link IIntensionConstraint}.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
final class IntensionConstraintXNodeAdapter implements IIntensionConstraint {

    /**
     * The mapping between {@link TypeExpr} and unary operators.
     */
    private static final Map<TypeExpr, UniverseOperator> UNARY_OPERATORS = Map.of(
            TypeExpr.NEG, UniverseArithmeticOperator.NEG,
            TypeExpr.ABS, UniverseArithmeticOperator.ABS,
            TypeExpr.SQR, UniverseArithmeticOperator.SQR,
            TypeExpr.NOT, UniverseBooleanOperator.NOT);

    /**
     * The mapping between {@link TypeExpr} and binary operators.
     */
    private static final Map<TypeExpr, UniverseOperator> BINARY_OPERATORS = Map.ofEntries(
            Map.entry(TypeExpr.SUB, UniverseArithmeticOperator.SUB),
            Map.entry(TypeExpr.DIV, UniverseArithmeticOperator.DIV),
            Map.entry(TypeExpr.MOD, UniverseArithmeticOperator.MOD),
            Map.entry(TypeExpr.POW, UniverseArithmeticOperator.POW),
            Map.entry(TypeExpr.DIST, UniverseArithmeticOperator.DIST),
            Map.entry(TypeExpr.IMP, UniverseBooleanOperator.IMPL),
            Map.entry(TypeExpr.LT, UniverseRelationalOperator.LT),
            Map.entry(TypeExpr.LE, UniverseRelationalOperator.LE),
            Map.entry(TypeExpr.EQ, UniverseRelationalOperator.EQ),
            Map.entry(TypeExpr.NE, UniverseRelationalOperator.NEQ),
            Map.entry(TypeExpr.GE, UniverseRelationalOperator.GE),
            Map.entry(TypeExpr.GT, UniverseRelationalOperator.GT),
            Map.entry(TypeExpr.IN, UniverseSetBelongingOperator.IN),
            Map.entry(TypeExpr.NOTIN, UniverseSetBelongingOperator.NOT_IN));

    /**
     * The mapping between {@link TypeExpr} and n-ary operators.
     */
    private static final Map<TypeExpr, UniverseOperator> NARY_OPERATORS = Map.of(
            TypeExpr.ADD, UniverseArithmeticOperator.ADD,
            TypeExpr.MUL, UniverseArithmeticOperator.MULT,
            TypeExpr.MIN, UniverseArithmeticOperator.MIN,
            TypeExpr.MAX, UniverseArithmeticOperator.MAX,
            TypeExpr.AND, UniverseBooleanOperator.AND,
            TypeExpr.OR, UniverseBooleanOperator.OR,
            TypeExpr.XOR, UniverseBooleanOperator.XOR,
            TypeExpr.IFF, UniverseBooleanOperator.EQUIV);

    /**
     * The adapted {@link XNode}.
     */
    private final XNode<?> adaptee;

    /**
     * Creates a new IntensionConstraintXNodeAdapter.
     *
     * @param adaptee The {@link XNode} to adapt.
     */
    IntensionConstraintXNodeAdapter(XNode<?> adaptee) {
        this.adaptee = adaptee;
    }

    /*
     * (non-Javadoc)
     *
     * @see org.sat4j.csp.constraints.intension.IIntensionConstraint#accept(org.sat4j.csp.
     * constraints.encoder.intension.IIntensionConstraintVisitor)
     */
    @Override
    public void accept(IIntensionConstraintVisitor visitor) throws UniverseContradictionException {
        var type = adaptee.type;

        if (type == TypeExpr.LONG) {
            // The adapted node is a constant.
            var self = new ConstantIntensionConstraint(BigInteger.valueOf(adaptee.val(0)));
            self.accept(visitor);
            return;
        }

        if (type == TypeExpr.VAR) {
            // The adapted node is a variable.
            var self = new VariableIntensionConstraint(adaptee.var(0).id());
            self.accept(visitor);
            return;
        }

        if (type == TypeExpr.IF) {
            // The adapted node is an alternative.
            var adaptedCondition = new IntensionConstraintXNodeAdapter(adaptee.sons[0]);
            var adaptedIfTrue = new IntensionConstraintXNodeAdapter(adaptee.sons[1]);
            var adaptedIfFalse = new IntensionConstraintXNodeAdapter(adaptee.sons[2]);
            var self = new IfThenElseIntensionConstraint(adaptedCondition, adaptedIfTrue,
                    adaptedIfFalse);
            self.accept(visitor);
            return;
        }

        var unary = UNARY_OPERATORS.get(type);
        if (unary != null) {
            // The adapted node is a unary constraint.
            var adaptedChild = new IntensionConstraintXNodeAdapter(adaptee.sons[0]);
            var self = new UnaryIntensionConstraint(unary, adaptedChild);
            self.accept(visitor);
            return;
        }

        var binary = BINARY_OPERATORS.get(type);
        if (binary != null) {
            // The adapted node is a binary constraint.
            var adaptedLeft = new IntensionConstraintXNodeAdapter(adaptee.sons[0]);
            var adaptedRight = new IntensionConstraintXNodeAdapter(adaptee.sons[1]);
            var self = new BinaryIntensionConstraint(binary, adaptedLeft, adaptedRight);
            self.accept(visitor);
            return;
        }

        var nary = NARY_OPERATORS.get(type);
        if (nary != null) {
            // The adapted node is an n-ary constraint.
            var adaptedChildren = Stream.of(adaptee.sons).map(
                    IntensionConstraintXNodeAdapter::new).collect(toList());
            var self = new NaryIntensionConstraint(nary, adaptedChildren);
            self.accept(visitor);
            return;
        }

        // The node is of an unsupported type.
        throw new UnsupportedOperationException("Unknown intension constraint of type: " + type);
    }

}
