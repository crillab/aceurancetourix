/**
 * Aceurancetourix, the JUniverse adapter for ACE.
 * Copyright (c) 2022 - Univ Artois, CNRS & Exakis Nelite.
 * All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 3 of the License, or (at your option) any later version.
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

package fr.univartois.cril.aceurancetourix;

import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.xcsp.common.IVar;
import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;

import fr.univartois.cril.juniverse.csp.intension.IUniverseIntensionConstraintVisitor;
import fr.univartois.cril.juniverse.csp.intension.UniverseBinaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseConstantIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseIfThenElseIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseNaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseRangeIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseSetIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseUnaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseVariableIntensionConstraint;
import fr.univartois.cril.juniverse.csp.operator.UniverseOperator;

/**
 * The AceIntensionConstraintVisitor is an {@link IUniverseIntensionConstraintVisitor} allowing to
 * convert an intension constraint to an {@link XNode}, which is the object recognized by
 * ACE.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class AceIntensionConstraintVisitor implements IUniverseIntensionConstraintVisitor {

    /**
     * ACE's Head.
     */
    private AceHead head;

    /**
     * The stack of the built {@link XNode} instances.
     */
    private Deque<XNode<IVar>> stack;


    /**
     * Creates a new AceIntensionConstraintVisitor.
     */
    AceIntensionConstraintVisitor(AceHead h) {
        stack = new LinkedList<>();
        head = h;
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.UnaryIntensionConstraint)
     */
    @Override
    public void visit(UniverseUnaryIntensionConstraint constr) {
        var xnode = stack.pop();
        TypeExpr op = toTypeExpr(constr.getOperator());
        stack.push(XNodeParent.build(op, xnode));
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.BinaryIntensionConstraint)
     */
    @Override
    public void visit(UniverseBinaryIntensionConstraint constr) {
        var right = stack.pop();
        var left = stack.pop();
        stack.push(XNodeParent.build(toTypeExpr(constr.getOperator()), left, right));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.NaryIntensionConstraint)
     */
    @Override
    public void visit(UniverseNaryIntensionConstraint constr) {
        int arity = constr.getArity();
        Object[] sons = new XNode[arity];
        for (int i = 0; i < arity; i++) {
            sons[i] = stack.pop();
        }
        stack.push(XNodeParent.build(toTypeExpr(constr.getOperator()), sons));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.IfThenElseIntensionConstraint)
     */
    @Override
    public void visit(UniverseIfThenElseIntensionConstraint ifThenElse) {
        var iffalse = stack.pop();
        var iftrue = stack.pop();
        var condition = stack.pop();

        stack.push(XNodeParent.build(TypeExpr.IF, condition, iftrue, iffalse));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.VariableIntensionConstraint)
     */
    @Override
    public void visit(UniverseVariableIntensionConstraint variable) {
        stack.push(new XNodeLeaf<>(TypeExpr.VAR, head.xcsp3.getVariable(variable.getIdentifier())));

    }

    /*
     * (non-Javadoc)
     *
     * @see
     * fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(Universefr.
     * univartois.cril.juniverse.csp.intension.ConstantIntensionConstraint)
     */
    @Override
    public void visit(UniverseConstantIntensionConstraint constant) {
        stack.push(new XNodeLeaf<>(TypeExpr.LONG, constant.getValue().longValue()));

    }

    /**
     * Gives the representation of the visited intension constraint as an ACE object.
     *
     * @return The tree representing the intension constraint encoded as an ACE object.
     */
    <T extends XNode<IVar>> T getTree() {
        return (T) stack.getFirst();
    }

    /**
     * Converts a {@link UniverseOperator} into {@link TypeExpr}.
     *
     * @param operator The operator to convert.
     *
     * @return The {@link TypeExpr} representing the operator.
     */
    protected TypeExpr toTypeExpr(UniverseOperator operator) {
        String string = operator.toString();
        TypeExpr op = null;
        switch (string) {
            case "NEQ":
                op = TypeExpr.NE;
                break;
            case "MULT":
                op = TypeExpr.MUL;
                break;
            case "IMPL":
                op = TypeExpr.IMP;
                break;
            case "EQUIV":
                op = TypeExpr.IFF;
                break;
            case "NOT_IN":
                op = TypeExpr.NOTIN;
                break;
            default:
                op = TypeExpr.valueOf(string);
                break;
        }
        return op;
    }

    @Override
    public void visit(UniverseRangeIntensionConstraint rangeIntensionConstraint) {
        stack.push(XNodeParent.set(new Range(rangeIntensionConstraint.getMin().intValue(),rangeIntensionConstraint.getMax().intValue()+1)));
    }

    @Override
    public void visit(UniverseSetIntensionConstraint setIntensionConstraint) {
        List<Long> values =new ArrayList<>(setIntensionConstraint.size());
        for(int i=0;i<setIntensionConstraint.size();i++) {
            var value = (XNodeLeaf<IVar>)stack.pop();
            values.add((Long)value.value);
        }
        stack.push(XNodeParent.set(values));
    }

}
