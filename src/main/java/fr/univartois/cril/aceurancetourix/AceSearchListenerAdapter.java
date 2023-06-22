/**
 * This file is a part of the {@code fr.univartois.cril.aceurancetourix} package.
 *
 * It contains the type AceSearchListenerAdapter.
 *
 * (c) 2023 Romain Wallon - aceurancetourix.
 * All rights reserved.
 */

package fr.univartois.cril.aceurancetourix;

import java.math.BigInteger;
import java.util.HashMap;

import constraints.Constraint;
import fr.univartois.cril.juniverse.core.problem.IUniverseVariable;
import fr.univartois.cril.juniverse.listener.IUniverseSearchListener;
import interfaces.Observers.ObserverOnAssignments;
import interfaces.Observers.ObserverOnConflicts;
import interfaces.Observers.ObserverOnDecisions;
import interfaces.Observers.ObserverOnRuns;
import interfaces.Observers.ObserverOnSolution;
import interfaces.Observers.ObserverOnSolving;
import variables.Variable;

/**
 * The AceSearchListenerAdapter
 *
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class AceSearchListenerAdapter implements ObserverOnAssignments, ObserverOnConflicts,
        ObserverOnDecisions, ObserverOnRuns, ObserverOnSolution, ObserverOnSolving {

    private final IUniverseSearchListener adaptee;

    private final JUniverseAceProblemAdapter solver;

    private int currentLevel;

    /**
     * Creates a new AceSearchListenerAdapter.
     *
     * @param adaptee
     */
    public AceSearchListenerAdapter(IUniverseSearchListener adaptee,
            JUniverseAceProblemAdapter solver) {
        this.adaptee = adaptee;
        this.solver = solver;
    }
    
    
    /**
     * Gives the adaptee of this AceSearchListenerAdapter.
     *
     * @return This AceSearchListenerAdapter's adaptee.
     */
    public IUniverseSearchListener getAdaptee() {
        return adaptee;
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnSolution#handleNewSolution()
     */
    @Override
    public void handleNewSolution() {
        var solution = solver.mapSolution();
        var solutionVar = new HashMap<IUniverseVariable, BigInteger>();
        for (var assignment : solution.entrySet()) {
            solutionVar.put(solver.getVariablesMapping().get(assignment.getKey()),
                    assignment.getValue());
        }
        if (solver.getHead().solver.problem.optimizer != null) {
            adaptee.onSolutionFound(solutionVar,
                    BigInteger.valueOf(solver.getHead().solver.solutions.bestBound));
        } else {
            adaptee.onSolutionFound(solutionVar);
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnConflicts#whenBacktrack()
     */
    @Override
    public void whenBacktrack() {
        currentLevel--;
        adaptee.onBacktrack(currentLevel);
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnConflicts#whenWipeout(constraints.Constraint,
     * variables.Variable)
     */
    @Override
    public void whenWipeout(Constraint arg0, Variable arg1) {
        adaptee.onConflict(new JUniverseAceConstraintAdapter(arg0),
                solver.getVariablesMapping().get(arg1.id()));
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnAssignments#afterAssignment(variables.Variable,
     * int)
     */
    @Override
    public void afterAssignment(Variable arg0, int arg1) {
        adaptee.onAssignment(new JUniverseVariableAceAdapter(arg0), BigInteger.valueOf(arg1));
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnAssignments#afterFailedAssignment(variables.
     * Variable, int)
     */
    @Override
    public void afterFailedAssignment(Variable arg0, int arg1) {
        adaptee.onFailedAssignment(new JUniverseVariableAceAdapter(arg0), BigInteger.valueOf(arg1));
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * interfaces.Observers.ObserverOnAssignments#afterUnassignment(variables.Variable)
     */
    @Override
    public void afterUnassignment(Variable arg0) {
        adaptee.onUnassignment(new JUniverseVariableAceAdapter(arg0));
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnSolving#afterSolving()
     */
    @Override
    public void afterSolving() {
        adaptee.end(solver.getResult());
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnSolving#beforeSolving()
     */
    @Override
    public void beforeSolving() {
        adaptee.start();
    }

    /*
     * (non-Javadoc)
     *
     * @see interfaces.Observers.ObserverOnRuns#afterRun()
     */
    @Override
    public void afterRun() {
        adaptee.onRestart();
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * interfaces.Observers.ObserverOnDecisions#beforeNegativeDecision(variables.Variable,
     * int)
     */
    @Override
    public void beforeNegativeDecision(Variable x, int a) {
        adaptee.onNegativeDecision(new JUniverseVariableAceAdapter(x), BigInteger.valueOf(a));
    }

    /*
     * (non-Javadoc)
     *
     * @see
     * interfaces.Observers.ObserverOnDecisions#beforePositiveDecision(variables.Variable,
     * int)
     */
    @Override
    public void beforePositiveDecision(Variable x, int a) {
        adaptee.onPositiveDecision(new JUniverseVariableAceAdapter(x), BigInteger.valueOf(a));
    }

}
