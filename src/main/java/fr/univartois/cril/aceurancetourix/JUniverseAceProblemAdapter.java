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
 * If not, see <http://www.gnu.org/licenses>.
 */

package fr.univartois.cril.aceurancetourix;

import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.binary;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.constant;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.eq;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.equiv;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.nary;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.neq;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.unary;
import static fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory.variable;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.xcsp.common.Condition;
import org.xcsp.common.Condition.ConditionIntset;
import org.xcsp.common.Condition.ConditionIntvl;
import org.xcsp.common.Condition.ConditionVal;
import org.xcsp.common.Condition.ConditionVar;
import org.xcsp.common.Constants;
import org.xcsp.common.IVar;
import org.xcsp.common.IVar.Var;
import org.xcsp.common.Range;
import org.xcsp.common.Types.TypeConditionOperatorRel;
import org.xcsp.common.Types.TypeConditionOperatorSet;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.common.Types.TypeObjective;
import org.xcsp.common.Types.TypeOperatorRel;
import org.xcsp.common.Types.TypeRank;
import org.xcsp.common.domains.Domains.Dom;
import org.xcsp.common.predicates.XNode;
import org.xcsp.common.predicates.XNodeParent;
import org.xcsp.common.structures.Automaton;
import org.xcsp.common.structures.Transition;
import org.xcsp.modeler.entities.VarEntities.VarAlone;
import org.xcsp.modeler.entities.VarEntities.VarEntity;

import dashboard.Control;
import fr.univartois.cril.aceurancetourix.reader.XCSP3Reader;
import fr.univartois.cril.juniverse.core.UniverseAssumption;
import fr.univartois.cril.juniverse.core.UniverseContradictionException;
import fr.univartois.cril.juniverse.core.UniverseSolverResult;
import fr.univartois.cril.juniverse.core.problem.IUniverseConstraint;
import fr.univartois.cril.juniverse.core.problem.IUniverseVariable;
import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;
import fr.univartois.cril.juniverse.csp.UniverseTransition;
import fr.univartois.cril.juniverse.csp.intension.IUniverseIntensionConstraint;
import fr.univartois.cril.juniverse.csp.intension.UniverseIntensionConstraintFactory;
import fr.univartois.cril.juniverse.csp.operator.UniverseArithmeticOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseBooleanOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator;
import fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator;
import fr.univartois.cril.juniverse.listener.IUniverseSearchListener;
import fr.univartois.cril.juniverse.optim.IUniverseOptimizationSolver;
import main.Head;
import problem.Problem;
import solver.AceBuilder;
import solver.Assumption;
import solver.Solver;
import solver.Solver.WarmStarter;
import variables.Variable;
import variables.Variable.VariableInteger;

/**
 * The JUniverseAceProblemAdapter adapts a {@link Head} (and a {@link Problem}) from ACE
 * to the {@link IUniverseCSPSolver} interface.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class JUniverseAceProblemAdapter implements IUniverseCSPSolver, IUniverseOptimizationSolver {

    /**
     * The adapted {@link Head}.
     */
    private AceHead head;

    public static int currentGroup;

    public static boolean inGroup;

    private int[][] previousArray;
    private boolean previousStarred;

    private List<List<BigInteger>> previousList;

    private UniverseSolverResult result;
    /**
     * Creates a new JUniverseAceProblemAdapter.
     */
    public JUniverseAceProblemAdapter() {
        // Nothing to do here.
    }

    /**
     * Gives the adapted Head.
     *
     * @return The adapted {@link Head}.
     */
    public AceHead getHead() {
        if (head == null) {
            head = new AceHead();
        }
        return head;
    }

    /**
     * Gives the builder used to configure the ACE solver.
     *
     * @return The builder of the solver.
     */
    public AceBuilder getBuilder() {
        return getHead().getBuilder();
    }

    /**
     * Gives the control of the solver.
     *
     * @return The control of the solver.
     */
    Control getControl() {
        return getHead().control;
    }

    @Override
    public void addAtLeast(List<Integer> arg0, List<Integer> arg1, int arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()),
                arg0.stream().map(BigInteger::valueOf).collect(Collectors.toList()),
                UniverseRelationalOperator.GE,
                BigInteger.valueOf(arg2));
    }

    @Override
    public void addAtLeast(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()), arg1,
                UniverseRelationalOperator.GE,
                arg2);
    }

    @Override
    public void addAtMost(List<Integer> arg0, List<Integer> arg1, int arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()),
                arg0.stream().map(BigInteger::valueOf).collect(Collectors.toList()),
                UniverseRelationalOperator.LE,
                BigInteger.valueOf(arg2));

    }

    @Override
    public void addAtMost(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()), arg1,
                UniverseRelationalOperator.LE,
                arg2);

    }

    @Override
    public void addExactly(List<Integer> arg0, List<Integer> arg1, int arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()),
                arg0.stream().map(BigInteger::valueOf).collect(Collectors.toList()),
                UniverseRelationalOperator.EQ,
                BigInteger.valueOf(arg2));

    }

    @Override
    public void addExactly(List<Integer> arg0, List<BigInteger> arg1, BigInteger arg2) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()), arg1,
                UniverseRelationalOperator.EQ,
                arg2);

    }

    @Override
    public void addPseudoBoolean(List<Integer> arg0, List<BigInteger> arg1, boolean arg2,
            BigInteger arg3) {
        addSum(arg0.stream().map(String::valueOf).collect(Collectors.toList()), arg1,
                arg2 ? UniverseRelationalOperator.LE : UniverseRelationalOperator.GE, arg3);

    }

    @Override
    public void addClause(List<Integer> arg0) {
        List<String> pos = new ArrayList<>();
        List<String> neg = new ArrayList<>();

        for (var i : arg0) {
            if (i < 0) {
                neg.add(String.valueOf(-i));
            } else {
                pos.add(i.toString());
            }
        }

        addClause(pos, neg);
    }

    @Override
    public UniverseSolverResult solveBoolean(List<UniverseAssumption<Boolean>> arg0) {
        List<UniverseAssumption<BigInteger>> assumpts = new ArrayList<>();

        for (var a : arg0) {
            assumpts.add(new UniverseAssumption<>(a.getVariableId(), a.isEqual(),
                    a.getValue() ? BigInteger.ONE : BigInteger.ZERO));
        }

        return solve(assumpts);
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
        Solver solver = getHead().getSolver();
        solver.restoreProblem();
        solver.stopping = null;
        solver.solutions.found = 0;
        solver.solutions.last = null;
        solver.nRecursiveRuns=0;
    }

    @Override
    public void setLogFile(String arg0) {
        try {
            System.setOut(new PrintStream(new File(arg0)));
        } catch (FileNotFoundException e) {
            throw new UncheckedIOException(e);
        }

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.IUniverseSolver#addSearchListener(fr.univartois.cril.juniverse.listener.IUniverseSearchListener)
     */
    @Override
    public void addSearchListener(IUniverseSearchListener listener) {
        var observer = new AceSearchListenerAdapter(listener, this);

        getHead().getSolver().observersOnSolution.add(observer);
        getHead().getSolver().observersOnAssignments.add(observer);
        getHead().getSolver().observersOnConflicts.add(observer);
        getHead().getSolver().observersOnRuns.add(observer);
        getHead().getSolver().observersOnSolving.add(observer);
        getHead().getSolver().observersOnDecisions.add(observer);
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.IUniverseSolver#removeSearchListener(fr.univartois.cril.juniverse.listener.IUniverseSearchListener)
     */
    @Override
    @SuppressWarnings({"rawtypes", "unchecked"})
    public void removeSearchListener(IUniverseSearchListener listener) {
        Predicate p = l -> (l instanceof AceSearchListenerAdapter)
                && (((AceSearchListenerAdapter) l).getAdaptee() == listener);

        getHead().getSolver().observersOnSolution.removeIf(p);
        getHead().getSolver().observersOnAssignments.removeIf(p);
        getHead().getSolver().observersOnConflicts.removeIf(p);
        getHead().getSolver().observersOnRuns.removeIf(p);
        getHead().getSolver().observersOnSolving.removeIf(p);
        getHead().getSolver().observersOnDecisions.removeIf(p);
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
        if (getHead().getSolver().solutions.found == 0) {
            throw new IllegalStateException("No solution found !");
        }
        List<BigInteger> sol = new ArrayList<>();
        for (int v : getHead().getSolver().solutions.last) {
            sol.add(BigInteger.valueOf(v));
        }
        return sol;
    }

    @Override
    public Map<String, BigInteger> mapSolution() {
        return mapSolution(false);
    }

    @Override
    public Map<String, BigInteger> mapSolution(boolean excludeAux) {
        if (getHead().getSolver().solutions.found == 0) {
            throw new IllegalStateException("No solution found !");
        }
        Map<String, BigInteger> sol = new HashMap<>();

        for (VarEntity va : getHead().problem.varEntities.allEntities) {
            if (excludeAux && va.id.startsWith(Problem.AUXILIARY_VARIABLE_PREFIX)) {
                continue;
            }

            if (va instanceof VarAlone) {
                Variable x = (Variable) ((VarAlone) va).var;
                if (getHead().problem.features.collecting.variables.contains(x)) {
                    sol.put(x.id(), BigInteger.valueOf(
                            x.dom.toVal(getHead().getSolver().solutions.last[x.num])));
                }
            }

        }
        return sol;
    }

    @Override
    public UniverseSolverResult solve() {
        result = getHead().isSatisfiable();
        return result;
    }

    @Override
    public UniverseSolverResult solve(String arg0) {
        loadInstance(arg0);
        return solve();
    }

    /**
     * @param filename
     */
    @Override
    public void loadInstance(String filename) {
        XCSP3Reader reader = new XCSP3Reader(this);
        try {
            reader.parseInstance(filename);
        } catch (UniverseContradictionException | IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public UniverseSolverResult solve(List<UniverseAssumption<BigInteger>> arg0) {

        List<Assumption> assumpts = new ArrayList<>();
        for (UniverseAssumption<BigInteger> assumpt : arg0) {
            int id = ((Variable) toVar(assumpt.getVariableId())).num;
            assumpts.add(new Assumption(id, assumpt.isEqual(),
                    assumpt.getValue().intValueExact()));
        }
        result = getHead().isSatisfiable(assumpts);
        return result;
    }


    /**
     * Gives the result of this JUniverseAceProblemAdapter.
     *
     * @return This JUniverseAceProblemAdapter's result.
     */
    UniverseSolverResult getResult() {
        return result;
    }

    @Override
    public void addAllDifferent(List<String> arg0) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferent(toVarArray(vars)));

    }

    @Override
    public void addAllDifferent(List<String> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] except = toIntArray(arg1);
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferent(toVarArray(vars), except));
    }

    @Override
    public void addAllDifferentIntension(List<IUniverseIntensionConstraint> arg0)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferent(toXnode(arg0)));
    }

    @Override
    public void addAllDifferentList(List<List<String>> arg0) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferentList(toVarMatrix(arg0)));

    }

    @Override
    public void addAllDifferentMatrix(List<List<String>> arg0)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferentMatrix(toVarMatrix(arg0)));
    }

    @Override
    public void addAllDifferentMatrix(List<List<String>> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        int[] except = toIntArray(arg1);
        getHead().xcsp3.addConstraintsToAdd(p -> p.allDifferentMatrix(toVarMatrix(arg0), except));

    }

    @Override
    public void addAllEqual(List<String> arg0) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.allEqual(toVarArray(vars)));

    }

    @Override
    public void addAllEqualIntension(List<IUniverseIntensionConstraint> arg0)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.allEqual(toXnode(arg0)));

    }

    @Override
    public void addAmong(List<String> arg0, List<BigInteger> arg1, BigInteger arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, arg1, UniverseRelationalOperator.EQ, arg2);
    }

    @Override
    public void addAmong(List<String> arg0, List<BigInteger> arg1, String arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, arg1, UniverseRelationalOperator.EQ, arg2);
    }

    @Override
    public void addAtLeast(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, List.of(arg1), UniverseRelationalOperator.GE, arg2);

    }

    @Override
    public void addAtMost(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, List.of(arg1), UniverseRelationalOperator.LE, arg2);

    }

    @Override
    public void addCardinalityWithConstantValuesAndConstantCounts(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, boolean arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toIntArray(arg1), arg3, toIntArray(arg2)));

    }

    @Override
    public void addCardinalityWithConstantValuesAndConstantIntervalCounts(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, List<BigInteger> arg3, boolean arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toIntArray(arg1), arg4, toIntArray(arg2),
                        toIntArray(arg3)));

    }

    @Override
    public void addCardinalityWithConstantValuesAndVariableCounts(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, boolean arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toIntArray(arg1), arg3, toVarArray(arg2)));

    }

    @Override
    public void addCardinalityWithVariableValuesAndConstantCounts(List<String> arg0,
            List<String> arg1, List<BigInteger> arg2, boolean arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toVarArray(arg1), arg3, toIntArray(arg2)));

    }

    @Override
    public void addCardinalityWithVariableValuesAndConstantIntervalCounts(List<String> arg0,
            List<String> arg1, List<BigInteger> arg2, List<BigInteger> arg3, boolean arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toVarArray(arg1), arg4, toIntArray(arg2),
                        toIntArray(arg3)));

    }

    @Override
    public void addCardinalityWithVariableValuesAndVariableCounts(List<String> arg0,
            List<String> arg1, List<String> arg2, boolean arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cardinality(toVarArray(arg0), toVarArray(arg1), arg3, toVarArray(arg2)));

    }

    @Override
    public void addChannel(List<String> arg0, int arg1) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.channel(toVarArray(arg0), arg1));
    }

    @Override
    public void addChannel(List<String> arg0, int arg1, String arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.channel(toVarArray(arg0), arg1, toVar(arg2)));

    }

    @Override
    public void addChannel(List<String> arg0, int arg1, List<String> arg2, int arg3)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.channel(toVarArray(arg0), arg1, toVarArray(arg2), arg3));
    }

    @Override
    public void addClause(List<String> arg0, List<String> arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.clause(toVarArray(arg0), toVarArray(arg1)));
    }

    @Override
    public void addCountIntensionWithConstantValues(List<IUniverseIntensionConstraint> arg0,
            List<BigInteger> arg1, UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toXnode(arg0), toIntArray(arg1), toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addCountIntensionWithConstantValues(List<IUniverseIntensionConstraint> arg0,
            List<BigInteger> arg1, UniverseRelationalOperator arg2, String arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toXnode(arg0), toIntArray(arg1), toCondition(arg2, arg3)));
    }

    @Override
    public void addCountWithConstantValues(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toVarArray(arg0), toIntArray(arg1),
                        toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addCountWithConstantValues(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toVarArray(arg0), toIntArray(arg1), toCondition(arg2, arg3)));
    }

    @Override
    public void addCountWithVariableValues(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toVarArray(arg0), toVarArray(arg1),
                        toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addCountWithVariableValues(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.count(toVarArray(arg0), toVarArray(arg1), toCondition(arg2, arg3)));

    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, UniverseRelationalOperator arg3,
            BigInteger arg4) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), null,
                        toIntArray(arg2), new ConditionVal(toOperator(arg3), arg4.longValue())));
    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<BigInteger> arg2, UniverseRelationalOperator arg3,
            String arg4) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), null,
                        toIntArray(arg2), new ConditionVar(toOperator(arg3), toVar(arg4))));
    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<BigInteger> arg3,
            UniverseRelationalOperator arg4, BigInteger arg5)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), toVarArray(arg2),
                        toIntArray(arg3), new ConditionVal(toOperator(arg4), arg5.longValue())));
    }

    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<BigInteger> arg3,
            UniverseRelationalOperator arg4, String arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), toVarArray(arg2),
                        toIntArray(arg3), new ConditionVar(toOperator(arg4), toVar(arg5))));
    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, UniverseRelationalOperator arg3,
            BigInteger arg4) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), null,
                        toVarArray(arg2), new ConditionVal(toOperator(arg3), arg4.longValue())));
    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, UniverseRelationalOperator arg3, String arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), null,
                        toVarArray(arg2), new ConditionVar(toOperator(arg3), toVar(arg4))));
    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<String> arg3,
            UniverseRelationalOperator arg4, BigInteger arg5)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), toVarArray(arg2),
                        toVarArray(arg3), new ConditionVal(toOperator(arg4), arg5.longValue())));
    }

    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> arg0,
            List<BigInteger> arg1, List<String> arg2, List<String> arg3,
            UniverseRelationalOperator arg4, String arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toIntArray(arg1), toVarArray(arg2),
                        toVarArray(arg3), new ConditionVar(toOperator(arg4), toVar(arg5))));
    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<BigInteger> arg2, UniverseRelationalOperator arg3, BigInteger arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), null,
                        toIntArray(arg2), new ConditionVal(toOperator(arg3), arg4.longValue())));
    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<BigInteger> arg2, UniverseRelationalOperator arg3, String arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), null,
                        toIntArray(arg2), new ConditionVar(toOperator(arg3), toVar(arg4))));
    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<BigInteger> arg3, UniverseRelationalOperator arg4,
            BigInteger arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), toVarArray(arg2),
                        toIntArray(arg3), new ConditionVal(toOperator(arg4), arg5.longValue())));
    }

    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<BigInteger> arg3, UniverseRelationalOperator arg4, String arg5)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), toVarArray(arg2),
                        toIntArray(arg3), new ConditionVar(toOperator(arg4), toVar(arg5))));
    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, UniverseRelationalOperator arg3, BigInteger arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), null,
                        toVarArray(arg2), new ConditionVal(toOperator(arg3), arg4.longValue())));
    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, UniverseRelationalOperator arg3, String arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), null,
                        toVarArray(arg2), new ConditionVar(toOperator(arg3), toVar(arg4))));

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<String> arg3, UniverseRelationalOperator arg4, BigInteger arg5)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), toVarArray(arg2),
                        toVarArray(arg3), new ConditionVal(toOperator(arg4), arg5.longValue())));

    }

    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> arg0, List<String> arg1,
            List<String> arg2, List<String> arg3, UniverseRelationalOperator arg4, String arg5)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.cumulative(toVarArray(arg0), toVarArray(arg1), toVarArray(arg2),
                        toVarArray(arg3), new ConditionVar(toOperator(arg4), toVar(arg5))));
    }

    @Override
    public void addElement(List<String> arg0,UniverseRelationalOperator operator,  BigInteger arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toVarArray(arg0),
                toCondition(operator, arg1.intValue())));
    }

    @Override
    public void addElement(List<String> arg0,UniverseRelationalOperator operator,  String arg1) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toVarArray(arg0),
                toCondition(operator, arg1)));
    }

    @Override
    public void addElement(List<String> arg0, int arg1, String arg2, UniverseRelationalOperator operator, BigInteger arg3)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toVarArray(arg0), arg1, toVar(arg2),
                TypeRank.ANY, toCondition(operator, arg3.intValue())));
    }

    @Override
    public void addElement(List<String> arg0, int arg1, String arg2, UniverseRelationalOperator operator, String arg3)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toVarArray(arg0), arg1, toVar(arg2),
                TypeRank.ANY, toCondition(operator, arg3)));
    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> arg0, int arg1, String arg2,
            int arg3, String arg4, UniverseRelationalOperator operator, BigInteger arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toIntMatrix(arg0), arg1, toVar(arg2),
                arg3,
                toVar(arg4), toCondition(operator, arg5.intValue())));
    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> arg0, int arg1, String arg2,
            int arg3, String arg4, UniverseRelationalOperator operator, String arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toIntMatrix(arg0), arg1, toVar(arg2), arg3,
                        toVar(arg4), toCondition(operator, arg5)));

    }

    @Override
    public void addElementConstantValues(List<BigInteger> arg0, int arg1, String arg2,UniverseRelationalOperator operator,
            BigInteger arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toIntArray(arg0), arg1, toVar(arg2),
                TypeRank.ANY, toCondition(operator, arg3.intValue())));

    }

    @Override
    public void addElementConstantValues(List<BigInteger> arg0, int arg1, String arg2, UniverseRelationalOperator operator, String arg3)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toIntArray(arg0), arg1, toVar(arg2),
                TypeRank.ANY, toCondition(operator, arg3)));

    }

    @Override
    public void addElementMatrix(List<List<String>> arg0, int arg1, String arg2, int arg3,
            String arg4,UniverseRelationalOperator operator,  BigInteger arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.element(toVarMatrix(arg0), arg1, toVar(arg2),
                arg3,
                toVar(arg4), toCondition(operator, arg5.intValue())));

    }

    @Override
    public void addElementMatrix(List<List<String>> arg0, int arg1, String arg2, int arg3,
            String arg4, UniverseRelationalOperator operator, String arg5) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarMatrix(arg0), arg1, toVar(arg2), arg3,
                        toVar(arg4), toCondition(operator, arg5)));
    }

    @Override
    public void addExactly(List<String> arg0, BigInteger arg1, BigInteger arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, List.of(arg1), UniverseRelationalOperator.EQ, arg2);
    }

    @Override
    public void addExactly(List<String> arg0, BigInteger arg1, String arg2)
            throws UniverseContradictionException {
        addCountWithConstantValues(arg0, List.of(arg1), UniverseRelationalOperator.EQ, arg2);
    }

    @Override
    public void addInstantiation(String arg0, int arg1) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.instantiation(new Var[] { toVar(arg0) }, arg1));
    }

    @Override
    public void addInstantiation(String arg0, BigInteger arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.instantiation(new Var[] { toVar(arg0) }, arg1.intValue()));

    }

    @Override
    public void addInstantiation(List<String> arg0, List<? extends Number> arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.instantiation(toVarArray(arg0), toIntArray(arg1)));
    }

    @Override
    public void addIntension(IUniverseIntensionConstraint arg0) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.intension(toXnode(arg0)));

    }

    @Override
    public void addLex(List<List<String>> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.lex(toVarMatrix(arg0), toOperatorRel(arg1)));
    }

    @Override
    public void addLexMatrix(List<List<String>> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.lexMatrix(toVarMatrix(arg0), toOperatorRel(arg1)));

    }

    @Override
    public void addLogical(UniverseBooleanOperator arg0, List<String> arg1)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.intension(
                toXnode(nary(arg0,
                        arg1.stream().map(UniverseIntensionConstraintFactory::variable).collect(Collectors.toList())))));

    }

    @Override
    public void addLogical(String arg0, boolean arg1, UniverseBooleanOperator arg2,
            List<String> arg3) throws UniverseContradictionException {
        if (arg1) {
            getHead().xcsp3.addConstraintsToAdd(p -> p.intension(toXnode(equiv(variable(arg0),
                    nary(arg2,
                            arg3.stream().map(UniverseIntensionConstraintFactory::variable).collect(Collectors.toList()))))));
        } else {
            getHead().xcsp3.addConstraintsToAdd(p -> p.intension(toXnode(neq(variable(arg0),
                    nary(arg2,
                            arg3.stream().map(UniverseIntensionConstraintFactory::variable).collect(Collectors.toList()))))));
        }
    }

    @Override
    public void addLogical(String arg0, String arg1, UniverseRelationalOperator arg2,
            BigInteger arg3) throws UniverseContradictionException {

        getHead().xcsp3.addConstraintsToAdd(p -> p.intension(
                toXnode(equiv(variable(arg0), binary(arg2, variable(arg1), constant(arg3))))));
    }

    @Override
    public void addLogical(String arg0, String arg1, UniverseRelationalOperator arg2, String arg3)
            throws UniverseContradictionException {

        getHead().xcsp3.addConstraintsToAdd(p -> p.intension(
                toXnode(equiv(variable(arg0), binary(arg2, variable(arg1), variable(arg3))))));
    }

    @Override
    public void addMaximum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximum(toVarArray(arg0), toCondition(arg1, arg2.intValue())));
    }

    @Override
    public void addMaximum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximum(toVarArray(arg0), toCondition(arg1, arg2)));
    }

    @Override
    public void addMaximumIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximum(toXnode(arg0), toCondition(arg1, arg2.intValue())));
    }

    @Override
    public void addMaximumIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximum(toXnode(arg0), toCondition(arg1, arg2)));
    }

    @Override
    public void addMinimum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimum(toVarArray(arg0), toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addMinimum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimum(toVarArray(arg0), toCondition(arg1, arg2)));
    }

    @Override
    public void addMinimumIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimum(toXnode(arg0), toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addMinimumIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.minimum(toXnode(arg0), toCondition(arg1, arg2)));

    }

    @Override
    public void addMultiDimensionalNoOverlap(List<List<String>> arg0, List<List<BigInteger>> arg1,
            boolean arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.noOverlap(toVarMatrix(arg0), toIntMatrix(arg1), true));

    }

    @Override
    public void addMultiDimensionalNoOverlapVariableLength(List<List<String>> arg0,
            List<List<String>> arg1) throws UniverseContradictionException {
        addMultiDimensionalNoOverlapVariableLength(arg0, arg1, true);

    }

    @Override
    public void addMultiDimensionalNoOverlapVariableLength(List<List<String>> arg0,
            List<List<String>> arg1, boolean arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.noOverlap(toVarMatrix(arg0), toVarMatrix(arg1), arg2));

    }

    @Override
    public void addMultiDimensionalNoOverlap(List<List<String>> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        addMultiDimensionalNoOverlap(arg0, arg1, true);
    }

    @Override
    public void addNValues(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.nValues(toVarArray(arg0), toCondition(arg1, arg2.intValue())));
    }

    @Override
    public void addNValues(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.nValues(toVarArray(arg0), toCondition(arg1, arg2)));

    }

    @Override
    public void addNValuesExcept(List<String> arg0, UniverseRelationalOperator arg1,
            BigInteger arg2, List<BigInteger> arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.nValues(toVarArray(arg0), toCondition(arg1, arg2.intValue()),
                        toIntArray(arg3)));

    }

    @Override
    public void addNValuesExcept(List<String> arg0, UniverseRelationalOperator arg1, String arg2,
            List<BigInteger> arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.nValues(toVarArray(arg0), toCondition(arg1, arg2), toIntArray(arg3)));
    }

    @Override
    public void addNValuesIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, BigInteger arg2)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.nValues(toXnode(arg0), toCondition(arg1, arg2.intValue())));
    }

    @Override
    public void addNValuesIntension(List<IUniverseIntensionConstraint> arg0,
            UniverseRelationalOperator arg1, String arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> p.nValues(toXnode(arg0), toCondition(arg1, arg2)));

    }

    @Override
    public void addNoOverlap(List<String> arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        addNoOverlap(arg0, arg1, true);

    }

    @Override
    public void addNoOverlap(List<String> arg0, List<BigInteger> arg1, boolean arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.noOverlap(toVarArray(arg0), toIntArray(arg1), arg2));
    }

    @Override
    public void addNoOverlapVariableLength(List<String> arg0, List<String> arg1)
            throws UniverseContradictionException {
        addNoOverlapVariableLength(arg0, arg1, true);
    }

    @Override
    public void addNoOverlapVariableLength(List<String> arg0, List<String> arg1, boolean arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.noOverlap(toVarArray(arg0), toVarArray(arg1), arg2));
    }

    @Override
    public void addNotAllEqual(List<String> arg0) throws UniverseContradictionException {
        addNValues(arg0, UniverseRelationalOperator.GT, BigInteger.ONE);
    }

    @Override
    public void addOrdered(List<String> arg0, UniverseRelationalOperator arg1)
            throws UniverseContradictionException {
        int[] lengths = new int[arg0.size() - 1];
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.ordered(toVarArray(arg0), lengths, toOperatorRel(arg1)));

    }

    @Override
    public void addOrderedWithConstantLength(List<String> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.ordered(toVarArray(arg0), toIntArray(arg1), toOperatorRel(arg2)));
    }

    @Override
    public void addOrderedWithVariableLength(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2) throws UniverseContradictionException {

        getHead().xcsp3.addConstraintsToAdd(
                p -> p.ordered(toVarArray(arg0), toVarArray(arg1), toOperatorRel(arg2)));
    }

    @Override
    public void addPrimitive(String arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        int[] coeffs = { 1 };
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(List.of(arg0)), coeffs, toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addPrimitive(UniverseArithmeticOperator arg0, String arg1, String arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            IUniverseIntensionConstraint left = unary(arg0, variable(arg1));
            IUniverseIntensionConstraint right = variable(arg2);
            p.intension(toXnode(eq(left, right)));
        });
    }

    @Override
    public void addPrimitive(String arg0, UniverseSetBelongingOperator arg1, List<BigInteger> arg2)
            throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            if (arg1 == UniverseSetBelongingOperator.IN) {
                p.intension(XNodeParent.in(toVar(arg0),
                        arg2.stream().map(BigInteger::intValue).collect(Collectors.toList())));
            } else {
                p.intension(XNodeParent.notin(toVar(arg0),
                        arg2.stream().map(BigInteger::intValue).collect(Collectors.toList())));
            }
        });
    }

    @Override
    public void addPrimitive(String arg0, UniverseSetBelongingOperator arg1, BigInteger arg2,
            BigInteger arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            if (arg1 == UniverseSetBelongingOperator.IN) {
                p.intension(XNodeParent.in(toVar(arg0),
                        new Range(arg2.intValue(), arg3.intValue() + 1)));
            } else {
                p.intension(XNodeParent.notin(toVar(arg0),
                        new Range(arg2.intValue(), arg3.intValue() + 1)));
            }
        });
    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, BigInteger arg2,
            UniverseRelationalOperator arg3, BigInteger arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            IUniverseIntensionConstraint left = binary(arg1, variable(arg0), constant(arg2));
            IUniverseIntensionConstraint right = constant(arg4);
            p.intension(toXnode(binary(arg3, left, right)));
        });
    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, String arg2,
            UniverseRelationalOperator arg3, BigInteger arg4)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            IUniverseIntensionConstraint left = binary(arg1,
                    variable(arg0),
                    variable(arg2));
            IUniverseIntensionConstraint right = constant(arg4.longValue());
            p.intension(toXnode(binary(arg3, left, right)));
        });

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, BigInteger arg2,
            UniverseRelationalOperator arg3, String arg4) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            IUniverseIntensionConstraint left = binary(arg1,
                    variable(arg0),
                    constant(arg2.longValue()));
            IUniverseIntensionConstraint right = variable(arg4);
            p.intension(toXnode(binary(arg3, left, right)));
        });

    }

    @Override
    public void addPrimitive(String arg0, UniverseArithmeticOperator arg1, String arg2,
            UniverseRelationalOperator arg3, String arg4) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            IUniverseIntensionConstraint left = binary(arg1,
                    variable(arg0),
                    variable(arg2));
            IUniverseIntensionConstraint right = variable(arg4);
            p.intension(toXnode(binary(arg3, left, right)));
        });
    }

    @Override
    public void addSum(List<String> arg0, UniverseRelationalOperator arg1, BigInteger arg2)
            throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs, toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addSum(List<String> arg0, UniverseRelationalOperator arg1, String arg2)
            throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs, toCondition(arg1, arg2)));

    }

    @Override
    public void addSum(List<String> arg0, List<BigInteger> arg1, UniverseRelationalOperator arg2,
            BigInteger arg3) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs, toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addSum(List<String> arg0, List<BigInteger> arg1, UniverseRelationalOperator arg2,
            String arg3) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs, toCondition(arg2, arg3)));
    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> arg0, UniverseRelationalOperator arg1,
            BigInteger arg2) throws UniverseContradictionException {
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(arg0), coeffs, toCondition(arg1, arg2.intValue())));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> arg0, UniverseRelationalOperator arg1,
            String arg2) throws UniverseContradictionException {
        int[] coeffs = new int[arg0.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(arg0), coeffs, toCondition(arg1, arg2)));
    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(arg0), toIntArray(arg1), toCondition(arg2, arg3.intValue())));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(arg0), toIntArray(arg1), toCondition(arg2, arg3)));
    }

    @Override
    public void addSumWithVariableCoefficients(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), toVarArray(arg1), toCondition(arg2, arg3.intValue())));
    }

    @Override
    public void addSumWithVariableCoefficients(List<String> arg0, List<String> arg1,
            UniverseRelationalOperator arg2, String arg3) throws UniverseContradictionException {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), toVarArray(arg1), toCondition(arg2, arg3)));
    }

    @Override
    public void addSupport(String arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        var t = new int[arg1.size()];
        toTuples(arg1, t);

        getHead().xcsp3.addConstraintsToAdd(p -> p.extension((Variable) toVar(arg0), t, true));
    }

    @Override
    public void addSupport(List<String> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        int[][] t;
        boolean starred;
        if(arg1==previousList) {
            t=previousArray;
            starred=previousStarred;
        }else {
            t= new int[arg1.size()][arg1.get(0).size()];
            starred= toTuples(arg1, t);
            previousList=arg1;
            previousArray=t;
            previousStarred=starred;
        }

        getHead().xcsp3.addConstraintsToAdd(p -> p.extension(toVarArray(arg0), t, true, starred));

    }

    @Override
    public void addConflicts(String arg0, List<BigInteger> arg1)
            throws UniverseContradictionException {
        var t = new int[arg1.size()];
        toTuples(arg1, t);

        getHead().xcsp3.addConstraintsToAdd(p -> p.extension((Variable) toVar(arg0), t, false));

    }

    @Override
    public void addConflicts(List<String> arg0, List<List<BigInteger>> arg1)
            throws UniverseContradictionException {
        int[][] t;
        boolean starred;
        if(arg1==previousList) {
            t=previousArray;
            starred=previousStarred;
        }else {
            t= new int[arg1.size()][arg1.get(0).size()];
            starred= toTuples(arg1, t);
            previousList=arg1;
            previousArray=t;
            previousStarred=starred;
        }
        getHead().xcsp3.addConstraintsToAdd(p -> p.extension(toVarArray(arg0), t, false, starred));

    }

    @Override
    public void maximizeExpression(IUniverseIntensionConstraint arg0) {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            var node = toXnode(arg0);
            if (node instanceof IVar) {
                p.maximize((IVar) node);
            } else {
                p.maximize(node);
            }
        });
    }

    @Override
    public void maximizeExpressionMaximum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MAXIMUM, toXnode(arg0)));
    }

    @Override
    public void maximizeExpressionMaximum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MAXIMUM, toXnode(arg0), coeffs));
    }

    @Override
    public void maximizeExpressionMinimum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MINIMUM, toXnode(arg0)));
    }

    @Override
    public void maximizeExpressionMinimum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MINIMUM, toXnode(arg0), coeffs));
    }

    @Override
    public void maximizeExpressionNValues(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.NVALUES, toXnode(arg0)));
    }

    @Override
    public void maximizeExpressionNValues(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.NVALUES, toXnode(arg0), coeffs));
    }

    @Override
    public void maximizeExpressionProduct(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.PRODUCT, toXnode(arg0)));
    }

    @Override
    public void maximizeExpressionProduct(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.PRODUCT, toXnode(arg0), coeffs));
    }

    @Override
    public void maximizeExpressionSum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.SUM, toXnode(arg0)));
    }

    @Override
    public void maximizeExpressionSum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.SUM, toXnode(arg0), coeffs));
    }

    @Override
    public void maximizeMaximum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MAXIMUM, toVarArray(vars)));

    }

    @Override
    public void maximizeMaximum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MAXIMUM, toVarArray(vars), coeffs));

    }

    @Override
    public void maximizeMinimum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MINIMUM, toVarArray(vars)));

    }

    @Override
    public void maximizeMinimum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.MINIMUM, toVarArray(vars), coeffs));

    }

    @Override
    public void maximizeNValues(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.NVALUES, toVarArray(vars)));

    }

    @Override
    public void maximizeNValues(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.NVALUES, toVarArray(vars), coeffs));

    }

    @Override
    public void maximizeProduct(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.PRODUCT, toVarArray(vars)));

    }

    @Override
    public void maximizeProduct(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.PRODUCT, toVarArray(vars), coeffs));

    }

    @Override
    public void maximizeSum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(TypeObjective.SUM, toVarArray(vars)));

    }

    @Override
    public void maximizeSum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximize(TypeObjective.SUM, toVarArray(vars), coeffs));

    }

    @Override
    public void maximizeVariable(String arg0) {
        getHead().xcsp3.addConstraintsToAdd(p -> p.maximize(toVar(arg0)));
    }

    @Override
    public void minimizeExpression(IUniverseIntensionConstraint arg0) {
        getHead().xcsp3.addConstraintsToAdd(p -> {
            var node = toXnode(arg0);
            if (node instanceof IVar) {
                p.minimize((IVar) node);
            } else {
                p.minimize(node);
            }
        });
    }

    @Override
    public void minimizeExpressionMaximum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MAXIMUM, toXnode(arg0)));
    }

    @Override
    public void minimizeExpressionMaximum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MAXIMUM, toXnode(arg0), coeffs));
    }

    @Override
    public void minimizeExpressionMinimum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MINIMUM, toXnode(arg0)));
    }

    @Override
    public void minimizeExpressionMinimum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MINIMUM, toXnode(arg0), coeffs));
    }

    @Override
    public void minimizeExpressionNValues(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.NVALUES, toXnode(arg0)));
    }

    @Override
    public void minimizeExpressionNValues(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.NVALUES, toXnode(arg0), coeffs));
    }

    @Override
    public void minimizeExpressionProduct(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.PRODUCT, toXnode(arg0)));
    }

    @Override
    public void minimizeExpressionProduct(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.PRODUCT, toXnode(arg0), coeffs));
    }

    @Override
    public void minimizeExpressionSum(List<IUniverseIntensionConstraint> arg0) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.SUM, toXnode(arg0)));
    }

    @Override
    public void minimizeExpressionSum(List<IUniverseIntensionConstraint> arg0, List<BigInteger> arg1) {
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.SUM, toXnode(arg0), coeffs));
    }

    @Override
    public void minimizeMaximum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MAXIMUM, toVarArray(vars)));
    }

    @Override
    public void minimizeMaximum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MAXIMUM, toVarArray(vars), coeffs));
    }

    @Override
    public void minimizeMinimum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MINIMUM, toVarArray(vars)));
    }

    @Override
    public void minimizeMinimum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.MINIMUM, toVarArray(vars), coeffs));
    }

    @Override
    public void minimizeNValues(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.NVALUES, toVarArray(vars)));
    }

    @Override
    public void minimizeNValues(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.NVALUES, toVarArray(vars), coeffs));
    }

    @Override
    public void minimizeProduct(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.PRODUCT, toVarArray(vars)));
    }

    @Override
    public void minimizeProduct(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.PRODUCT, toVarArray(vars), coeffs));
    }

    @Override
    public void minimizeSum(List<String> arg0) {
        List<String> vars = new ArrayList<>(arg0);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.SUM, toVarArray(vars)));
    }

    @Override
    public void minimizeSum(List<String> arg0, List<BigInteger> arg1) {
        List<String> vars = new ArrayList<>(arg0);
        int[] coeffs = arg1.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimize(TypeObjective.SUM, toVarArray(vars), coeffs));
    }

    @Override
    public void minimizeVariable(String arg0) {
        getHead().xcsp3.addConstraintsToAdd(p -> p.minimize(toVar(arg0)));
    }

    @Override
    public void newVariable(String arg0, List<? extends Number> arg1) {

        int[] vals = new int[arg1.size()];
        for (int i = 0; i < vals.length; i++) {
            vals[i] = arg1.get(i).intValue();
        }

        getHead().xcsp3.addVariableToAdd(arg0, (p, s) -> {
            var x = p.buildVarInteger(s, new Dom(vals));
            getHead().xcsp3.imp().varEntities.newVarAloneEntity(s, x, null);
            return x;
        });
    }

    @Override
    public void newVariable(String arg0, int arg1, int arg2) {
        getHead().xcsp3.addVariableToAdd(arg0, (p, s) -> {
            var x = p.buildVarInteger(s, new Dom(arg1, arg2));
            getHead().xcsp3.imp().varEntities.newVarAloneEntity(s, x, null);
            return x;
        });
    }

    @Override
    public void newVariable(String arg0, BigInteger arg1, BigInteger arg2) {
        getHead().xcsp3.addVariableToAdd(arg0,
                (p, s) -> {
                    var x = p.buildVarInteger(s, new Dom(arg1.intValue(), arg2.intValue()));
                    getHead().xcsp3.imp().varEntities.newVarAloneEntity(s, x, null);
                    return x;
                });

    }

    @Override
    public void decisionVariables(List<String> variables) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.annotations.decision = toVariableArray(variables));
    }

    @Override
	public void valueHeuristicStatic(List<String> vars, List<? extends Number> order) {
		getHead().xcsp3.addConstraintsToAdd(p->p.staticValHeuristic(toVarArray(vars), toIntArray(order)));
	}


    /**
     * Creates an array of {@code int} values from a List of {@link Number}.
     *
     * @param values The lists of values to convert.
     *
     * @return The created array.
     */
    protected int[] toIntArray(List<? extends Number> values) {
        return values.stream().mapToInt(Number::intValue).toArray();
    }

    /**
     * Creates a matrix of {@code int} values from a matrix of {@link BigInteger}.
     *
     * @param values The lists of values to convert.
     *
     * @return The created matrix.
     */
    private int[][] toIntMatrix(List<List<BigInteger>> values) {
        return values.stream().map(this::toIntArray).toArray(int[][]::new);
    }

    /**
     * Creates an array of {@link Var} from the list of the corresponding variable names.
     *
     * @param variables The list of variable names to convert.
     *
     * @return The created array.
     */
    private Var[] toVarArray(List<String> variables) {
        Var[] vars = new Var[variables.size()];
        for (int i = 0; i < variables.size(); i++) {
            vars[i] = (Var) getHead().xcsp3.getVariable(variables.get(i));
        }
        return vars;
    }

    /**
     * Creates a matrix of {@link Var} from the lists of the corresponding variable names.
     *
     * @param variables The lists of variable names to convert.
     *
     * @return The created matrix.
     */
    private Var[][] toVarMatrix(List<List<String>> variables) {
        Variable[][] vars = new VariableInteger[variables.size()][];
        for (int i = 0; i < variables.size(); i++) {
            vars[i] = toVariableArray(variables.get(i));
        }
        return (Var[][]) vars;
    }

    /**
     * Creates an array of {@link Variable} from the list of the corresponding variable
     * names.
     *
     * @param variables The list of variable names to convert.
     *
     * @return The created array.
     */
    private Variable[] toVariableArray(List<String> variables) {
        Variable[] vars = new VariableInteger[variables.size()];
        for (int i = 0; i < variables.size(); i++) {
            vars[i] = getHead().xcsp3.getVariable(variables.get(i));
        }
        return vars;
    }

    /**
     * Gives the {@link Var} with the given name.
     *
     * @param v The name of the variable.
     * @return The {@link Var} with the given name.
     */
    private Var toVar(String v) {
        return (Var) getHead().xcsp3.getVariable(v);
    }

    /**
     * Creates an {@link XNodeParent} representing the given {@link IUniverseIntensionConstraint}.
     *
     * @param i The intension constraint to convert to an {@link XNodeParent}.
     * @return The created {@link XNodeParent}.
     */
    private <T extends XNode<IVar>> T toXnode(IUniverseIntensionConstraint i) {
        var visitor = new AceIntensionConstraintVisitor(getHead());
        i.accept(visitor);
        return visitor.getTree();
    }

    /**
     * Creates an {@link XNodeParent} array representing the given
     * {@link IUniverseIntensionConstraint} instances.
     *
     * @param i The intension constraints to convert to an {@link XNodeParent}.
     * @return The created {@link XNodeParent} array.
     */
    private XNode[] toXnode(List<IUniverseIntensionConstraint> list) {
        @SuppressWarnings("unchecked")
        XNode[] tab = new XNode[list.size()];
        for (int i = 0; i < list.size(); i++) {
            tab[i] = toXnode(list.get(i));
        }
        return tab;
    }

    /**
     * Converts a {@link BigInteger} tuple to an {@code int} array.
     *
     * @param tuple The tuple to convert.
     * @param t The output array.
     * @return Whether the tuple contains stars.
     */
    private boolean toTuples(List<BigInteger> tuple, int[] t) {
        boolean starred = false;
        for (int i = 0; i < tuple.size(); i++) {
            if (tuple.get(i) == null) {
                starred = true;
                t[i] = Constants.STAR;
                continue;
            }
            t[i] = tuple.get(i).intValue();
        }
        return starred;
    }

    /**
     * Converts a {@link BigInteger} tuple array to an {@code int} matrix.
     *
     * @param tuple The tuples to convert.
     * @param t The output matrix.
     * @return Whether the tuples contain stars.
     */
    private boolean toTuples(List<List<BigInteger>> tuples, int[][] t) {
        boolean starred = false;
        for (int i = 0; i < tuples.size(); i++) {
            starred |= toTuples(tuples.get(i), t[i]);
        }
        return starred;
    }

    /**
     * Creates a {@link Condition} from universe types.
     *
     * @param op The operator of the condition.
     * @param value The value of the condition.
     *
     * @return The created condition.
     */
    private Condition toCondition(UniverseRelationalOperator op, int value) {
        return new ConditionVal(toOperator(op), value);
    }

    /**
     * Creates a {@link Condition} from universe types.
     *
     * @param op The operator of the condition.
     * @param variable The variable of the condition.
     *
     * @return The created condition.
     */
    private Condition toCondition(UniverseRelationalOperator op, String variable) {
        return new ConditionVar(toOperator(op), toVar(variable));
    }

    /**
     * Gives the {@link TypeConditionOperatorRel} corresponding to the given operator.
     *
     * @param op The operator to convert.
     *
     * @return The {@link TypeConditionOperatorRel} corresponding to the given operator.
     */
    private TypeConditionOperatorRel toOperator(UniverseRelationalOperator op) {
        if (op == UniverseRelationalOperator.NEQ) {
            return TypeConditionOperatorRel.NE;
        }
        return TypeConditionOperatorRel.valueOf(op.toString());
    }

    /**
     * Gives the {@link TypeOperatorRel} corresponding to the given operator.
     *
     * @param op The operator to convert.
     *
     * @return The {@link TypeOperatorRel} corresponding to the given operator.
     */
    private TypeOperatorRel toOperatorRel(UniverseRelationalOperator op) {
        return TypeOperatorRel.valueOf(op.toString());
    }

    /**
     * Creates a {@link Condition} from universe types.
     *
     * @param op The operator of the condition.
     * @param value The value of the condition.
     *
     * @return The created condition.
     */
    private Condition toCondition(UniverseSetBelongingOperator op, int min, int max) {
        return new ConditionIntvl(toOperator(op), min, max);
    }

    /**
     * Creates a {@link Condition} from universe types.
     *
     * @param op The operator of the condition.
     * @param variable The variable of the condition.
     *
     * @return The created condition.
     */
    private Condition toCondition(UniverseSetBelongingOperator op, List<BigInteger> values) {
        return new ConditionIntset(toOperator(op), toIntArray(values));
    }

    /**
     * Gives the {@link TypeConditionOperatorRel} corresponding to the given operator.
     *
     * @param op The operator to convert.
     *
     * @return The {@link TypeConditionOperatorRel} corresponding to the given operator.
     */
    private TypeConditionOperatorSet toOperator(UniverseSetBelongingOperator op) {
        if (op == UniverseSetBelongingOperator.NOT_IN) {
            return TypeConditionOperatorSet.NOTIN;
        } else {
            return TypeConditionOperatorSet.IN;
        }
    }

    @Override
    public Map<String, IUniverseVariable> getVariablesMapping() {
        getHead().buildProblem(0);
        var map = new HashMap<String, IUniverseVariable>();
        for (var variable : getHead().problem.variables) {
            map.put(variable.id(), new JUniverseVariableAceAdapter(variable));
        }
        return map;
    }

    @Override
    public void addSum(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        List<String> vars = new ArrayList<>(variables);
        int[] coeffs = new int[variables.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs,
                        toCondition(operator, min.intValue(), max.intValue())));
    }

    @Override
    public void addSum(List<String> variables, List<BigInteger> coefficients,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        List<String> vars = new ArrayList<>(variables);
        int[] coeffs = coefficients.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs,
                        toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addSum(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> values) {
        List<String> vars = new ArrayList<>(variables);
        int[] coeffs = new int[variables.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs,
                        toCondition(operator, values)));

    }

    @Override
    public void addSum(List<String> variables, List<BigInteger> coefficients,
            UniverseSetBelongingOperator operator, List<BigInteger> values) {
        List<String> vars = new ArrayList<>(variables);
        int[] coeffs = coefficients.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), coeffs,
                        toCondition(operator, values)));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        int[] coeffs = new int[intensionConstraints.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(intensionConstraints), coeffs,
                        toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            List<BigInteger> coefficients, UniverseSetBelongingOperator operator, BigInteger min,
            BigInteger max) {
        int[] coeffs = coefficients.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(intensionConstraints), coeffs,
                        toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, List<BigInteger> values) {
        int[] coeffs = new int[intensionConstraints.size()];
        Arrays.fill(coeffs, 1);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(intensionConstraints), coeffs,
                        toCondition(operator, values)));

    }

    @Override
    public void addSumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            List<BigInteger> coefficients, UniverseSetBelongingOperator operator,
            List<BigInteger> values) {
        int[] coeffs = coefficients.stream().mapToInt(BigInteger::intValue).toArray();
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toXnode(intensionConstraints), coeffs,
                        toCondition(operator, values)));

    }
    @Override
    public void addSumWithVariableCoefficients(List<String> variables, List<String> coefficients,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        List<String> vars = new ArrayList<>(variables);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), toVarArray(coefficients),
                        toCondition(operator, min.intValue(),max.intValue())));

    }

    @Override
    public void addSumWithVariableCoefficients(List<String> variables, List<String> coefficients,
            UniverseSetBelongingOperator operator, List<BigInteger> values) {
        List<String> vars = new ArrayList<>(variables);
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.sum(toVarArray(vars), toVarArray(coefficients),
                        toCondition(operator, values)));

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(
            List<IUniverseIntensionConstraint> intensionConstraints, List<String> coefficients,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(
            List<IUniverseIntensionConstraint> intensionConstraints, List<String> coefficients,
            UniverseSetBelongingOperator operator, List<BigInteger> values) {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(List<IUniverseIntensionConstraint> arg0,
            List<String> arg1, UniverseRelationalOperator arg2, BigInteger arg3)
                    throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }

    @Override
    public void addSumIntensionWithVariableCoefficients(List<IUniverseIntensionConstraint> arg0,
            List<String> arg1, UniverseRelationalOperator arg2, String arg3)
                    throws UniverseContradictionException {
        throw new UnsupportedOperationException();

    }



    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBiDimensionalNoOverlap(java.util.List, java.util.List, java.util.List, java.util.List)
     */
    @Override
    public void addBiDimensionalNoOverlap(List<String> xVariables, List<String> yVariables,
            List<String> xLength, List<BigInteger> yLength) {
        addBiDimensionalNoOverlap(xVariables, yVariables, xLength, yLength, true);
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBiDimensionalNoOverlap(java.util.List, java.util.List, java.util.List, java.util.List, boolean)
     */
    @Override
    public void addBiDimensionalNoOverlap(List<String> xVariables, List<String> yVariables,
            List<String> xLength, List<BigInteger> yLength, boolean zeroIgnored) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.noOverlap(toVarArray(xVariables), toVarArray(yVariables), toVarArray(xLength), toIntArray(yLength), zeroIgnored));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addFlow(java.util.List, java.util.List, java.util.List)
     */
    @Override
    public void addFlow(List<String> list, List<BigInteger> balance, List<List<BigInteger>> edges) {
        getHead().xcsp3.addConstraintsToAdd(p->p.flow(toVarArray(list), toIntArray(balance), toIntMatrix(edges)));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addFlow(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addFlow(List<String> list, List<BigInteger> balance, List<List<BigInteger>> edges,
            List<BigInteger> weights, UniverseRelationalOperator operator, String variable) {
        getHead().xcsp3.addConstraintsToAdd(p->p.flow(toVarArray(list), toIntArray(balance), toIntMatrix(edges),toIntArray(weights),toCondition(operator, variable)));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addFlow(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addFlow(List<String> list, List<BigInteger> balance, List<List<BigInteger>> edges,
            List<BigInteger> weights, UniverseRelationalOperator operator, BigInteger value) {
        getHead().xcsp3.addConstraintsToAdd(p->p.flow(toVarArray(list), toIntArray(balance), toIntMatrix(edges),toIntArray(weights),toCondition(operator, value.intValue())));


    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addKnapsack(List<String> list, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, String wVariable, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, String pVariable) {
        getHead().xcsp3.addConstraintsToAdd(p->p.knapsack(toVarArray(list),toIntArray(weights), toCondition(wOperator, wVariable), toIntArray(profits), toCondition(pOperator, pVariable)));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> list, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, String wVariable, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, BigInteger pValue) {
        getHead().xcsp3.addConstraintsToAdd(p->p.knapsack(toVarArray(list),toIntArray(weights), toCondition(wOperator, wVariable), toIntArray(profits), toCondition(pOperator, pValue.intValue())));


    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addKnapsack(List<String> list, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, BigInteger wValue, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, String pVariable) {
        getHead().xcsp3.addConstraintsToAdd(p->p.knapsack(toVarArray(list),toIntArray(weights), toCondition(wOperator, wValue.intValue()), toIntArray(profits), toCondition(pOperator, pVariable)));


    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> list, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, BigInteger wValue, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, BigInteger pValue) {
        getHead().xcsp3.addConstraintsToAdd(p->p.knapsack(toVarArray(list),toIntArray(weights), toCondition(wOperator, wValue.intValue()), toIntArray(profits), toCondition(pOperator, pValue.intValue())));


    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addPrecedence(java.util.List)
     */
    @Override
    public void addPrecedence(List<String> list) {
        getHead().xcsp3.addConstraintsToAdd(p->p.precedence(toVarArray(list)));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addPrecedence(java.util.List, java.util.List, boolean)
     */
    @Override
    public void addPrecedence(List<String> list, List<BigInteger> values, boolean covered) {
        getHead().xcsp3.addConstraintsToAdd(p->p.precedence(toVarArray(list),toIntArray(values),covered));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addRegular(java.lang.String, java.util.List, java.util.List, java.lang.String, java.util.List)
     */
    @Override
    public void addRegular(List<String> list, List<UniverseTransition> transitions,
            String startState, List<String> finalStates) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.regular(toVarArray(list),new Automaton(startState, toTransition(transitions), finalStates.toArray(new String[finalStates.size()]))));

    }

    private Transition[] toTransition(List<UniverseTransition> transitions) {
        return transitions.stream().map(t->new Transition(t.getStart(),(long)t.getValue(),t.getEnd())).collect(Collectors.toList()).toArray(new Transition[transitions.size()]);
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMDD(java.lang.String, java.util.List, java.util.List)
     */
    @Override
    public void addMDD(List<String> list, List<UniverseTransition> transitions) {
        getHead().xcsp3.addConstraintsToAdd(p->p.mdd(toVarArray(list), toTransition(transitions)));
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCircuit(java.lang.String, java.util.List, int)
     */
    @Override
    public void addCircuit(List<String> list, int startIndex) {
        getHead().xcsp3.addConstraintsToAdd(p->p.circuit(toVarArray(list), startIndex));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCircuit(java.lang.String, java.util.List, int, int)
     */
    @Override
    public void addCircuit(List<String> list, int startIndex, BigInteger size) {
        getHead().xcsp3.addConstraintsToAdd(p->p.circuit(toVarArray(list), startIndex,size.intValue()));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCircuit(java.lang.String, java.util.List, int, java.lang.String)
     */
    @Override
    public void addCircuit(List<String> list, int startIndex, String size) {
        getHead().xcsp3.addConstraintsToAdd(p->p.circuit(toVarArray(list), startIndex,toVar(size)));
    }

    @Override
    public void setLowerBound(BigInteger lb) {
        getHead().getSolver().problem.optimizer.setAsyncMinBound(lb.longValue());
        if(getHead().getSolver().solutions.found>0) {
            var solution = solution();
            String stringSolution = solution.stream().map(BigInteger::toString).collect(
                    Collectors.joining(" "));
            getHead().getSolver().warmStarter = new WarmStarter(stringSolution, head.solver);
        }
    }

    @Override
    public void setUpperBound(BigInteger ub) {
        getHead().getSolver().problem.optimizer.setAsyncMaxBound(ub.longValue());
        if(getHead().getSolver().solutions.found>0) {
            var solution = solution();
            String stringSolution = solution.stream().map(BigInteger::toString).collect(
                    Collectors.joining(" "));
            getHead().getSolver().warmStarter = new WarmStarter(stringSolution, head.solver);
        }
    }

    @Override
    public void setBounds(BigInteger lb, BigInteger ub) {
        setLowerBound(lb);
        setUpperBound(ub);
    }

    @Override
    public BigInteger getCurrentBound() {
        return BigInteger.valueOf(getHead().getSolver().problem.optimizer.value());
    }

    @Override
    public boolean isMinimization() {
        return getHead().getSolver().problem.optimizer.minimization;
    }

    @Override
    public BigInteger getLowerBound() {
        return BigInteger.valueOf(getHead().getSolver().problem.optimizer.clb.limit());
    }

    @Override
    public BigInteger getUpperBound() {
        return BigInteger.valueOf(getHead().getSolver().problem.optimizer.cub.limit());
    }

    @Override
    public boolean isOptimization() {
        return getHead().getSolver().problem.framework==TypeFramework.COP;
    }

    @Override
    public void addElement(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarArray(variables), toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addElement(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> value) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarArray(variables), toCondition(operator, value)));

    }

    @Override
    public void addElementConstantValues(List<BigInteger> values, int startIndex, String index,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toIntArray(values),startIndex,toVar(index),TypeRank.ANY, toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addElementConstantValues(List<BigInteger> values, int startIndex, String index,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toIntArray(values),startIndex,toVar(index),TypeRank.ANY, toCondition(operator, set)));

    }

    @Override
    public void addElement(List<String> variables, int startIndex, String index,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarArray(variables),startIndex,toVar(index),TypeRank.ANY, toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addElement(List<String> values, int startIndex, String index,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarArray(values),startIndex,toVar(index),TypeRank.ANY, toCondition(operator, set)));

    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> matrix, int startRowIndex,
            String rowIndex, int startColIndex, String colIndex,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toIntMatrix(matrix),startRowIndex,toVar(rowIndex),startColIndex,toVar(colIndex), toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addElementConstantMatrix(List<List<BigInteger>> matrix, int startRowIndex,
            String rowIndex, int startColIndex, String colIndex,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toIntMatrix(matrix),startRowIndex,toVar(rowIndex),startColIndex,toVar(colIndex), toCondition(operator, set)));

    }

    @Override
    public void addElementMatrix(List<List<String>> matrix, int startRowIndex, String rowIndex,
            int startColIndex, String colIndex, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarMatrix(matrix),startRowIndex,toVar(rowIndex),startColIndex,toVar(colIndex), toCondition(operator, min.intValue(), max.intValue())));

    }

    @Override
    public void addElementMatrix(List<List<String>> matrix, int startRowIndex, String rowIndex,
            int startColIndex, String colIndex, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.element(toVarMatrix(matrix),startRowIndex,toVar(rowIndex),startColIndex,toVar(colIndex), toCondition(operator, set)));

    }

    @Override
    public void addMaximumArg(List<String> variables, UniverseRelationalOperator operator,
            BigInteger value) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, value.intValue())));

    }

    @Override
    public void addMaximumArg(List<String> variables, UniverseRelationalOperator operator,
            String variable) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, variable)));

    }

    @Override
    public void addMinimumArg(List<String> variables, UniverseRelationalOperator operator,
            BigInteger value) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, value.intValue())));

    }

    @Override
    public void addMinimumArg(List<String> variables, UniverseRelationalOperator operator,
            String variable) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, variable)));

    }

    @Override
    public void addMaximumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseRelationalOperator operator, BigInteger value) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, value.intValue())));

    }

    @Override
    public void addMaximumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseRelationalOperator operator, String variable) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, variable)));

    }

    @Override
    public void addMinimumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseRelationalOperator operator, BigInteger value) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, value.intValue())));

    }

    @Override
    public void addMinimumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseRelationalOperator operator, String variable) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, variable)));

    }

    @Override
    public void addMaximumArg(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, min.intValue(),max.intValue())));

    }

    @Override
    public void addMaximumArg(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, set)));

    }

    @Override
    public void addMinimumArg(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, min.intValue(),max.intValue())));

    }

    @Override
    public void addMinimumArg(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toVarArray(variables),TypeRank.ANY,toCondition(operator, set)));

    }

    @Override
    public void addMaximumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, min.intValue(),max.intValue())));

    }

    @Override
    public void addMaximumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.maximumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, set)));

    }

    @Override
    public void addMinimumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, min.intValue(),max.intValue())));

    }

    @Override
    public void addMinimumArgIntension(List<IUniverseIntensionConstraint> variables,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        getHead().xcsp3.addConstraintsToAdd(
                p -> p.minimumArg(toXnode(variables),TypeRank.ANY,toCondition(operator, set)));

    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#newVariableSymbolic(java.lang.String, java.util.List)
     */
    @Override
    public void newVariableSymbolic(String id, List<String> values) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addInstantiationSymbolic(java.lang.String, java.lang.String)
     */
    @Override
    public void addInstantiationSymbolic(String variable, String value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addInstantiationSymbolic(java.util.List, java.util.List)
     */
    @Override
    public void addInstantiationSymbolic(List<String> variables, List<String> values) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addAllDifferentList(java.util.List, java.util.List)
     */
    @Override
    public void addAllDifferentList(List<List<String>> variableLists,
            List<List<BigInteger>> except) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountWithConstantValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCountWithConstantValues(List<String> variables, List<BigInteger> values,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountWithConstantValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCountWithConstantValues(List<String> variables, List<BigInteger> values,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountWithVariableValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCountWithVariableValues(List<String> variables, List<String> values,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountWithVariableValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCountWithVariableValues(List<String> variables, List<String> values,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountIntensionWithConstantValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCountIntensionWithConstantValues(List<IUniverseIntensionConstraint> expressions,
            List<BigInteger> values, UniverseSetBelongingOperator operator, BigInteger min,
            BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCountIntensionWithConstantValues(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCountIntensionWithConstantValues(List<IUniverseIntensionConstraint> expressions,
            List<BigInteger> values, UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValues(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addNValues(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValuesExcept(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger, java.util.List)
     */
    @Override
    public void addNValuesExcept(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max, List<BigInteger> except) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValues(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addNValues(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValuesExcept(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List, java.util.List)
     */
    @Override
    public void addNValuesExcept(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set, List<BigInteger> except) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValuesIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addNValuesIntension(List<IUniverseIntensionConstraint> expressions,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addNValuesIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addNValuesIntension(List<IUniverseIntensionConstraint> expressions,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPacking(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addBinPacking(List<String> variables, List<BigInteger> sizes,
            UniverseRelationalOperator operator, BigInteger value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPacking(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addBinPacking(List<String> variables, List<BigInteger> sizes,
            UniverseRelationalOperator operator, String variable) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPacking(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addBinPacking(List<String> variables, List<BigInteger> sizes,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPacking(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addBinPacking(List<String> variables, List<BigInteger> sizes,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPackingWithConstantCapacities(java.util.List, java.util.List, java.util.List, boolean)
     */
    @Override
    public void addBinPackingWithConstantCapacities(List<String> variables, List<BigInteger> sizes,
            List<BigInteger> capacities, boolean loads) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addBinPackingWithVariableCapacities(java.util.List, java.util.List, java.util.List, boolean)
     */
    @Override
    public void addBinPackingWithVariableCapacities(List<String> variables, List<BigInteger> sizes,
            List<String> capacities, boolean loads) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsConstantHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> origins,
            List<BigInteger> lengths, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsConstantHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> origins,
            List<BigInteger> lengths, List<String> ends, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsConstantHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> origins,
            List<BigInteger> lengths, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsConstantHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeConstantLengthsConstantHeights(List<String> origins,
            List<BigInteger> lengths, List<String> ends, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsVariableHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> origins,
            List<BigInteger> lengths, List<String> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsVariableHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> origins,
            List<BigInteger> lengths, List<String> ends, List<String> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsVariableHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> origins,
            List<BigInteger> lengths, List<String> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeConstantLengthsVariableHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeConstantLengthsVariableHeights(List<String> origins,
            List<BigInteger> lengths, List<String> ends, List<String> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsConstantHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> origins,
            List<String> lengths, List<BigInteger> heights, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsConstantHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> origins,
            List<String> lengths, List<String> ends, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsConstantHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> origins,
            List<String> lengths, List<BigInteger> heights, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsConstantHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeVariableLengthsConstantHeights(List<String> origins,
            List<String> lengths, List<String> ends, List<BigInteger> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsVariableHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> origins,
            List<String> lengths, List<String> heights, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsVariableHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> origins,
            List<String> lengths, List<String> ends, List<String> heights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsVariableHeights(java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> origins,
            List<String> lengths, List<String> heights, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addCumulativeVariableLengthsVariableHeights(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addCumulativeVariableLengthsVariableHeights(List<String> origins,
            List<String> lengths, List<String> ends, List<String> heights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, BigInteger wValue, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, BigInteger pMin, BigInteger pMax) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, BigInteger wValue, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, List<BigInteger> pSet) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, String wVariable, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, BigInteger pMin, BigInteger pMax) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseRelationalOperator wOperator, String wVariable, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, List<BigInteger> pSet) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, BigInteger wMin, BigInteger wMax,
            List<BigInteger> profits, UniverseRelationalOperator pOperator, BigInteger pValue) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, BigInteger wMin, BigInteger wMax,
            List<BigInteger> profits, UniverseRelationalOperator pOperator, String pVariable) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, BigInteger wMin, BigInteger wMax,
            List<BigInteger> profits, UniverseSetBelongingOperator pOperator, BigInteger pMin,
            BigInteger pMax) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, BigInteger wMin, BigInteger wMax,
            List<BigInteger> profits, UniverseSetBelongingOperator pOperator,
            List<BigInteger> pSet) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, List<BigInteger> wSet, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, BigInteger pValue) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, List<BigInteger> wSet, List<BigInteger> profits,
            UniverseRelationalOperator pOperator, String pVariable) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, List<BigInteger> wSet, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, BigInteger pMin, BigInteger pMax) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addKnapsack(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addKnapsack(List<String> variables, List<BigInteger> weights,
            UniverseSetBelongingOperator wOperator, List<BigInteger> wSet, List<BigInteger> profits,
            UniverseSetBelongingOperator pOperator, List<BigInteger> pSet) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addStretch(java.util.List, java.util.List, java.util.List, java.util.List)
     */
    @Override
    public void addStretch(List<String> variables, List<BigInteger> values,
            List<BigInteger> widthsMin, List<BigInteger> widthsMax) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addStretch(java.util.List, java.util.List, java.util.List, java.util.List, java.util.List)
     */
    @Override
    public void addStretch(List<String> variables, List<BigInteger> values,
            List<BigInteger> widthsMin, List<BigInteger> widthsMax,
            List<List<BigInteger>> patterns) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addSupportSymbolic(java.lang.String, java.util.List)
     */
    @Override
    public void addSupportSymbolic(String variable, List<String> allowedValues) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addSupportSymbolic(java.util.List, java.util.List)
     */
    @Override
    public void addSupportSymbolic(List<String> variableTuple, List<List<String>> allowedValues) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addConflictsSymbolic(java.lang.String, java.util.List)
     */
    @Override
    public void addConflictsSymbolic(String variable, List<String> forbiddenValues) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addConflictsSymbolic(java.util.List, java.util.List)
     */
    @Override
    public void addConflictsSymbolic(List<String> variableTuple,
            List<List<String>> forbiddenValues) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimum(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMinimum(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimum(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMinimum(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addMinimumIndex(List<String> variables, int startIndex, String index,
            UniverseRelationalOperator operator, BigInteger value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addMinimumIndex(List<String> variables, int startIndex, String index,
            UniverseRelationalOperator operator, String value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMinimumIndex(List<String> variables, int startIndex, String index,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMinimumIndex(List<String> variables, int startIndex, String index,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMinimumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMinimumIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMinimumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximum(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMaximum(List<String> variables, UniverseSetBelongingOperator operator,
            BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximum(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMaximum(List<String> variables, UniverseSetBelongingOperator operator,
            List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.math.BigInteger)
     */
    @Override
    public void addMaximumIndex(List<String> variables, int startIndex, String index,
            UniverseRelationalOperator operator, BigInteger value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator, java.lang.String)
     */
    @Override
    public void addMaximumIndex(List<String> variables, int startIndex, String index,
            UniverseRelationalOperator operator, String value) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMaximumIndex(List<String> variables, int startIndex, String index,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIndex(java.util.List, int, java.lang.String, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMaximumIndex(List<String> variables, int startIndex, String index,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addMaximumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addMaximumIntension(java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addMaximumIntension(List<IUniverseIntensionConstraint> intensionConstraints,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addLex(java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseRelationalOperator)
     */
    @Override
    public void addLex(List<String> variables, List<BigInteger> limit,
            UniverseRelationalOperator operator) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addFlow(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.math.BigInteger, java.math.BigInteger)
     */
    @Override
    public void addFlow(List<String> variables, List<BigInteger> balance,
            List<List<BigInteger>> edges, List<BigInteger> weights,
            UniverseSetBelongingOperator operator, BigInteger min, BigInteger max) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.csp.IUniverseCSPSolver#addFlow(java.util.List, java.util.List, java.util.List, java.util.List, fr.univartois.cril.juniverse.csp.operator.UniverseSetBelongingOperator, java.util.List)
     */
    @Override
    public void addFlow(List<String> variables, List<BigInteger> balance,
            List<List<BigInteger>> edges, List<BigInteger> weights,
            UniverseSetBelongingOperator operator, List<BigInteger> set) {
        // TODO Auto-generated method stub.
        throw new UnsupportedOperationException();
    }

	@Override
	public void setLogStream(OutputStream stream) {
        throw new UnsupportedOperationException();
	}

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.IUniverseSolver#getAuxiliaryVariables()
     */
    @Override
    public List<String> getAuxiliaryVariables() {
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.IUniverseSolver#checkSolution()
     */
    @Override
    public boolean checkSolution() {
        throw new UnsupportedOperationException();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.IUniverseSolver#checkSolution(java.util.Map)
     */
    @Override
    public boolean checkSolution(Map<String, BigInteger> assignment) {
        throw new UnsupportedOperationException();
    }

	@Override
	public List<IUniverseConstraint> getConstraints() {
		return Stream.of(getHead().getSolver().problem.constraints).map(JUniverseAceConstraintAdapter::new).collect(Collectors.toList());
	}



}
