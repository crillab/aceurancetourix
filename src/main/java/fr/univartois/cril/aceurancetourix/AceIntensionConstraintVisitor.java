/**
 * JUniverse, a solver interface.
 * Copyright (c) 2022 - Univ Artois, CNRS & Exakis Nelite.
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

package fr.univartois.cril.aceurancetourix;

import java.util.Deque;
import java.util.LinkedList;

import org.xcsp.common.IVar;
import org.xcsp.common.Types.TypeExpr;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeLeaf;
import org.xcsp.common.predicates.XNodeParent;

import fr.univartois.cril.juniverse.csp.intension.BinaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.ConstantIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor;
import fr.univartois.cril.juniverse.csp.intension.IfThenElseIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.NaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UnaryIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.VariableIntensionConstraint;
import fr.univartois.cril.juniverse.csp.operator.UniverseOperator;


/**
 * The AceIntensionConstraintVisitor
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class AceIntensionConstraintVisitor implements IIntensionConstraintVisitor {
    
    
    private Deque<XNode<IVar>> stack;
    private AceHead head;
    /**
     * Creates a new AceIntensionConstraintVisitor.
     */
    AceIntensionConstraintVisitor(AceHead h) {
        stack = new LinkedList<>();
        head=h;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.UnaryIntensionConstraint)
     */
    @Override
    public void visit(UnaryIntensionConstraint constr) {
        var xnode = stack.pop();
        TypeExpr op = toTypeExpr(constr.getOperator());
        stack.push(XNodeParent.build(op,xnode));
      
    }

    /**
     * @param operator
     * @return
     */
    protected TypeExpr toTypeExpr(UniverseOperator operator) {
        String string = operator.toString();
        TypeExpr op =null;
        switch(string) {
            case "NEQ":
                op = TypeExpr.NE;
                break;
            case "MULT":
                op=TypeExpr.MUL;
                break;
            case "IMPL":
                op=TypeExpr.IMP;
                break;
            case "EQUIV":
                op=TypeExpr.IFF;
                break;
            default:
                op = TypeExpr.valueOf(string);
                break;
        }
        return op;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.BinaryIntensionConstraint)
     */
    @Override
    public void visit(BinaryIntensionConstraint constr) {
        var right = stack.pop();
        var left = stack.pop();
        stack.push(XNodeParent.build(toTypeExpr(constr.getOperator()), left,right));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.NaryIntensionConstraint)
     */
    @Override
    public void visit(NaryIntensionConstraint constr) {
        int arity = constr.getArity();
        Object[] sons = new XNode[arity];
        for(int i=0;i<arity;i++) {
            sons[i]=stack.pop();
        }
        stack.push(XNodeParent.build(toTypeExpr(constr.getOperator()), sons));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.IfThenElseIntensionConstraint)
     */
    @Override
    public void visit(IfThenElseIntensionConstraint ifThenElse) {
        var iffalse = stack.pop();
        var iftrue=stack.pop();
        var condition=stack.pop();
        
        stack.push(XNodeParent.build(TypeExpr.IF,condition,iftrue,iffalse));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.VariableIntensionConstraint)
     */
    @Override
    public void visit(VariableIntensionConstraint variable) {
        stack.push(new XNodeLeaf<>(TypeExpr.VAR, head.xcsp3.getVariable(variable.getIdentifier())));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.intension.IIntensionConstraintVisitor#visit(fr.univartois.cril.juniverse.csp.intension.ConstantIntensionConstraint)
     */
    @Override
    public void visit(ConstantIntensionConstraint constant) {
        stack.push(new XNodeLeaf<>(TypeExpr.LONG, constant.getValue().longValue()));

    }
    
    XNodeParent<IVar> getTree(){
        return (XNodeParent<IVar>) stack.getFirst();
    }

}

