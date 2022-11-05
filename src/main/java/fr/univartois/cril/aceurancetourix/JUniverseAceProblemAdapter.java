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

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.xcsp.common.Condition;
import org.xcsp.common.Condition.ConditionVal;
import org.xcsp.common.Condition.ConditionVar;
import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.domains.Domains.Dom;
import org.xcsp.common.predicates.XNodeParent;

import dashboard.Control;
import dashboard.Input;
import fr.univartois.cril.juniverse.core.UniverseAssumption;
import fr.univartois.cril.juniverse.core.UniverseContradictionException;
import fr.univartois.cril.juniverse.core.UniverseSolverResult;
import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;
import fr.univartois.cril.juniverse.csp.intension.IIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.IntensionConstraintFactory;
import fr.univartois.cril.juniverse.csp.operator.UniverseArithmeticOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseBooleanOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator;
import solver.AceBuilder;
import variables.Variable;

/**
 * The JUniverseAceProblemAdapter
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class JUniverseAceProblemAdapter implements IUniverseCSPSolver {

    private AceHead head;

    /**
     * Creates a new JUniverseAceProblemAdapter.
     */
    public JUniverseAceProblemAdapter() {
    }
    
    private AceHead getHead() {
        if (head == null) {
            head = new AceHead();
        }
        return head;
    }

    
    public AceBuilder getBuilder() {
        return getHead().getBuilder();
    }
    
    public static void main(String[] args) throws UniverseContradictionException {
        var h = new JUniverseAceProblemAdapter();
        h.getBuilder().getOptionsGeneralBuilder().setVerbose(-1);
        h.newVariable("x", 0, 10);
        h.newVariable("y", 0, 10);
        h.addIntension(IntensionConstraintFactory.neq(IntensionConstraintFactory.variable("x"), IntensionConstraintFactory.variable("y")));
        System.out.println(h.solve());
        System.out.println(h.solution());

    }

    Control getControl() {
        return getHead().control;
    }

    @Override
    public void addAtLeast(List<Integer> arg0, List<Integer> arg1, int arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAtLeast(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAtMost(List<Integer> arg0, List<Integer> arg1, int arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAtMost(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addExactly(List<Integer> arg0, List<Integer> arg1, int arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addExactly(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPseudoBoolean(List<Integer> arg0, List<BigInteger> arg1, boolean arg2,
            BigInteger arg3) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addClause(List<Integer> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public UniverseSolverResult solveBoolean(List<UniverseAssumption<Boolean>> arg0) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void interrupt() {
        getHead().interruptSearch();
    }

    @Override
    public int nConstraints() {
        return getHead().problem.constraints.length;
    }

    @Override
    public int nVariables() {
        return getHead().problem.variables.length;
    }

    @Override
    public void reset() {
        getHead().solver.restoreProblem();
    }

    @Override
    public void setLogFile(String arg0) {
        try {
            System.setOut(new PrintStream(new File(arg0)));
        } catch (FileNotFoundException e) {
            throw new UncheckedIOException(e);
        }

    }

    @Override
    public void setTimeout(long arg0) {
        setTimeoutMs(arg0 * 1000);

    }

    @Override
    public void setTimeoutMs(long arg0) {
        getBuilder().getOptionsGeneralBuilder().setTimeout(arg0);
    }

    @Override
    public void setVerbosity(int arg0) {
        getBuilder().getOptionsGeneralBuilder().setVerbose(arg0);
    }

    @Override
    public List<BigInteger> solution() {
        if (getHead().solver.solutions.found == 0) {
            throw new IllegalStateException("No solution found !");
        }
        List<BigInteger> sol = new ArrayList<>();
        for (int v : getHead().solver.solutions.last) {
            sol.add(BigInteger.valueOf(v));
        }
        return sol;
    }

    @Override
    public UniverseSolverResult solve() {
        return getHead().isSatisfiable();
    }

    @Override
    public UniverseSolverResult solve(String arg0) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void addAllDifferent(List<String> arg0) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferent(toVar(vars)));

    }

    @Override
    public void addAllDifferent(List<String> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllDifferentIntension(List<IIntensionConstraint> arg0)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllDifferentList(List<List<String>> arg0) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllDifferentMatrix(List<List<String>> arg0)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllDifferentMatrix(List<List<String>> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllEqual(List<String> arg0) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAllEqualIntension(List<IIntensionConstraint> arg0)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAmong(List<String> arg0, List<BigInteger> arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAmong(List<String> arg0, List<BigInteger> arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAtLeast(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addAtMost(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithConstantValuesAndConstantCounts(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, boolean arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithConstantValuesAndConstantIntervalCounts(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, List<BigInteger> arg3, boolean arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithConstantValuesAndVariableCounts(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, boolean arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithVariableValuesAndConstantCounts(List<String> arg0,
            List<String> arg1, List<BigInteger> arg2, boolean arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithVariableValuesAndConstantIntervalCounts(List<String> arg0,
            List<String> arg1, List<BigInteger> arg2, List<BigInteger> arg3, boolean arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCardinalityWithVariableValuesAndVariableCounts(List<String> arg0,
            List<String> arg1, List<String> arg2, boolean arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addChannel(List<String> arg0, int arg1) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addChannel(List<String> arg0, int arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addChannel(List<String> arg0, int arg1, List<String> arg2, int arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addClause(List<String> arg0, List<String> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addConflicts(String arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        var t = new int[arg1.size()];
        boolean starred = toTuples(arg1, t);
        if(starred) {
            throw new UnsupportedOperationException();
        }
        getHead().xcsp3.addConstraintsToAdd(p->p.extension((Variable)toVar(arg0), t, false));

    }

    @Override
    public void addConflicts(List<String> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        int[][] t = new int[arg0.size()][arg1.get(0).size()];
        boolean starred = toTuples(arg1, t);
        if(starred) {
            throw new UnsupportedOperationException();
        }
        getHead().xcsp3.addConstraintsToAdd(p->p.extension(toVar(arg0), t, false));

    }

    @Override
    public void addCountIntensionWithConstantValues(List<IIntensionConstraint> arg0,
            List<BigInteger> arg1, UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCountIntensionWithConstantValues(List<IIntensionConstraint> arg0,
            List<BigInteger> arg1, UniverseRelationalOperator arg2, String arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCountWithConstantValues(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCountWithConstantValues(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCountWithVariableValues(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCountWithVariableValues(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, UniverseRelationalOperator arg3,
            BigInteger arg4) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, UniverseRelationalOperator arg3,
            String arg4) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<BigInteger> arg3,
            UniverseRelationalOperator arg4, BigInteger arg5)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<BigInteger> arg3,
            UniverseRelationalOperator arg4, String arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, UniverseRelationalOperator arg3,
            BigInteger arg4) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, UniverseRelationalOperator arg3, String arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<String> arg3,
            UniverseRelationalOperator arg4, BigInteger arg5)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<String> arg3,
            UniverseRelationalOperator arg4, String arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<BigInteger> arg2, UniverseRelationalOperator arg3, BigInteger arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<BigInteger> arg2, UniverseRelationalOperator arg3, String arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<BigInteger> arg3, UniverseRelationalOperator arg4,
            BigInteger arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<BigInteger> arg3, UniverseRelationalOperator arg4, String arg5)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, UniverseRelationalOperator arg3, BigInteger arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, UniverseRelationalOperator arg3, String arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<String> arg3, UniverseRelationalOperator arg4, BigInteger arg5)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<String> arg3, UniverseRelationalOperator arg4, String arg5)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElement(List<String> arg0, BigInteger arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElement(List<String> arg0, String arg1) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElement(List<String> arg0, int arg1, String arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElement(List<String> arg0, int arg1, String arg2, String arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> arg0, int arg1, String arg2,
            int arg3, String arg4, BigInteger arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> arg0, int arg1, String arg2,
            int arg3, String arg4, String arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementConstantValues(List<BigInteger> arg0, int arg1, String arg2,
            BigInteger arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementConstantValues(List<BigInteger> arg0, int arg1, String arg2, String arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementMatrix(List<List<String>> arg0, int arg1, String arg2, int arg3,
            String arg4, BigInteger arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addElementMatrix(List<List<String>> arg0, int arg1, String arg2, int arg3,
            String arg4, String arg5) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addExactly(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addExactly(List<String> arg0, BigInteger arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addInstantiation(String arg0, int arg1) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addInstantiation(String arg0, BigInteger arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addInstantiation(List<String> arg0, List<? extends Number> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addIntension(IIntensionConstraint arg0) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p->p.intension(toXnode(arg0)));

    }

    @Override
    public void addLex(List<List<String>> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addLexMatrix(List<List<String>> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addLogical(UniverseBooleanOperator arg0, List<String> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addLogical(String arg0, boolean arg1, UniverseBooleanOperator arg2,
            List<String> arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addLogical(String arg0, String arg1, UniverseRelationalOperator arg2,
            BigInteger arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addLogical(String arg0, String arg1, UniverseRelationalOperator arg2, String arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMaximum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMaximum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMaximumIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMaximumIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMinimum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMinimum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMinimumIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMinimumIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMultiDimensionalNoOverlap(List<List<String>> arg0, List<List<BigInteger>> arg1,
            boolean arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMultiDimensionalNoOverlapVariableLength(List<List<String>> arg0,
            List<List<String>> arg1) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addMultiDimensionalNoOverlapVariableLength(List<List<String>> arg0,
            List<List<String>> arg1, boolean arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValues(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValues(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValuesExcept(List<String> arg0, UniverseRelationalOperator arg1,
            BigInteger arg2, List<BigInteger> arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValuesExcept(List<String> arg0, UniverseRelationalOperator arg1, String arg2,
            List<BigInteger> arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValuesIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNValuesIntension(List<IIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNoOverlap(List<String> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNoOverlap(List<String> arg0, List<BigInteger> arg1, boolean arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNoOverlapVariableLength(List<String> arg0, List<String> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNoOverlapVariableLength(List<String> arg0, List<String> arg1, boolean arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addNotAllEqual(List<String> arg0) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addOrdered(List<String> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addOrderedWithConstantLength(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addOrderedWithVariableLength(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        int[] coeffs = { 1 };
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVar(List.of(arg0)), coeffs, toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addPrimitive(UniverseArithmeticOperator arg0, String arg1, String arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseSetBelongingOperator arg1, List<BigInteger> arg2)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseSetBelongingOperator arg1, BigInteger arg2,
            BigInteger arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, BigInteger arg2,
            UniverseRelationalOperator arg3, BigInteger arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, String arg2,
            UniverseRelationalOperator arg3, BigInteger arg4)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, BigInteger arg2,
            UniverseRelationalOperator arg3, String arg4) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, String arg2,
            UniverseRelationalOperator arg3, String arg4) throws UniverseContradictionException {

    }

    @Override
    public void addSum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVar(vars), coeffs, toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addSum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVar(vars), coeffs, toCondition(arg1, arg2)));

    }

    @Override
    public void addSum(List<String> arg0, List<BigInteger> arg1, UniverseRelationalOperator arg2,
            BigInteger arg3) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVar(vars), coeffs, toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addSum(List<String> arg0, List<BigInteger> arg1, UniverseRelationalOperator arg2,
            String arg3) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVar(vars), coeffs, toCondition(arg2, arg3)));
    }

    @Override
    public void addSumIntension(List<IIntensionConstraint> arg0, UniverseRelationalOperator arg1,
            BigInteger arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntension(List<IIntensionConstraint> arg0, UniverseRelationalOperator arg1,
            String arg2) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntension(List<IIntensionConstraint> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntension(List<IIntensionConstraint> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(List<IIntensionConstraint> arg0,
            List<String> arg1, UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(List<IIntensionConstraint> arg0,
            List<String> arg1, UniverseRelationalOperator arg2, String arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumWithVariableCoefficients(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumWithVariableCoefficients(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSupport(String arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        var t = new int[arg1.size()];
        boolean starred = toTuples(arg1, t);
        if(starred) {
            throw new UnsupportedOperationException();
        }
        getHead().xcsp3.addConstraintsToAdd(p->p.extension((Variable)toVar(arg0), t, true));
    }

    @Override
    public void addSupport(List<String> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        int[][] t = new int[arg0.size()][arg1.get(0).size()];
        boolean starred = toTuples(arg1, t);
        if(starred) {
            throw new UnsupportedOperationException();
        }
        getHead().xcsp3.addConstraintsToAdd(p->p.extension(toVar(arg0), t, true));

    }

    @Override
    public void addeMultiDimensionalNoOverlap(List<List<String>> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpression(IIntensionConstraint arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionMaximum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionMaximum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionMinimum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionMinimum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionNValues(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionNValues(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionProduct(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionProduct(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionSum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeExpressionSum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void maximizeMaximum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.MAXIMUM, toVar(vars)));

    }

    @Override
    public void maximizeMaximum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MAXIMUM, toVar(vars), coeffs));

    }

    @Override
    public void maximizeMinimum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.MINIMUM, toVar(vars)));

    }

    @Override
    public void maximizeMinimum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MINIMUM, toVar(vars), coeffs));

    }

    @Override
    public void maximizeNValues(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.NVALUES, toVar(vars)));

    }

    @Override
    public void maximizeNValues(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.NVALUES, toVar(vars), coeffs));

    }

    @Override
    public void maximizeProduct(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.PRODUCT, toVar(vars)));

    }

    @Override
    public void maximizeProduct(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.PRODUCT, toVar(vars), coeffs));

    }

    @Override
    public void maximizeSum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.SUM, toVar(vars)));

    }

    @Override
    public void maximizeSum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(x -> x.intValue()).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.SUM, toVar(vars), coeffs));

    }

    @Override
    public void maximizeVariable(String arg0) {
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(toVar(arg0)));
    }

    @Override
    public void minimizeExpression(IIntensionConstraint arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionMaximum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionMaximum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionMinimum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionMinimum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionNValues(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionNValues(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionProduct(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionProduct(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionSum(List<IIntensionConstraint> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeExpressionSum(List<IIntensionConstraint> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeMaximum(List<String> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeMaximum(List<String> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeMinimum(List<String> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeMinimum(List<String> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeNValues(List<String> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeNValues(List<String> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeProduct(List<String> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeProduct(List<String> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeSum(List<String> arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeSum(List<String> arg0, List<BigInteger> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void minimizeVariable(String arg0) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void newVariable(String arg0, List<? extends Number> arg1) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void newVariable(String arg0, int arg1, int arg2) {
        getHead().xcsp3.addVariableToAdd(arg0, (p, s) -> p.buildVarInteger(s, new Dom(arg1, arg2)));
    }

    @Override
    public void newVariable(String arg0, BigInteger arg1, BigInteger arg2) {
        getHead().xcsp3.addVariableToAdd(arg0,
                (p, s) -> p.buildVarInteger(s, new Dom(arg1.intValue(), arg2.intValue())));

    }

    private Var[] toVar(List<String> variables) {
        Var[] vars = new Var[variables.size()];
        for (int i = 0; i < variables.size(); i++) {
            vars[i] = getHead().xcsp3.getVariable(variables.get(i));
        }
        return vars;
    }

    private Var toVar(String v) {
        return getHead().xcsp3.getVariable(v);
    }

    private XNodeParent<IVar> toXnode(IIntensionConstraint i) {
        var visitor = new AceIntensionConstraintVisitor(getHead());
        i.accept(visitor);
        return visitor.getTree();
    }

    private XNodeParent<IVar>[] toXnode(List<IIntensionConstraint> list) {
        XNodeParent<IVar>[] tab = new XNodeParent[list.size()];
        for (int i = 0; i < list.size(); i++) {
            tab[i] = toXnode(list.get(i));
        }
        return tab;
    }
    
    private boolean toTuples(List<BigInteger> tuple,int[] t) {
        boolean starred = false;
        for(int i=0;i<tuple.size();i++) {
            if(tuple.get(i)==null) {
                starred=true;
                t[i]=Constants.STAR;
                continue;
            }
            t[i]=tuple.get(i).intValue();
        }
        return starred;
    }
    
    private boolean toTuples(List<List<BigInteger>> tuples, int[][] t) {
        boolean starred = false;
        for(int i=0;i<tuples.size();i++) {
            starred|=toTuples(tuples.get(i),t[i]);
        }
        return starred;
    }

    private Condition toCondition(UniverseRelationalOperator op, int value) {
        return new ConditionVal(toOperator(op), value);
    }

    private Condition toCondition(UniverseRelationalOperator op, String value) {
        return new ConditionVar(toOperator(op), toVar(value));
    }

    private TypeConditionOperatorRel toOperator(UniverseRelationalOperator op) {
        if (op == UniverseRelationalOperator.NEQ) {
            return TypeConditionOperatorRel.NE;
        }
        return TypeConditionOperatorRel.valueOf(op.toString());
    }

}
