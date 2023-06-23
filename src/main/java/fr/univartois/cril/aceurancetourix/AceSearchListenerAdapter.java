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
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class AceSearchListenerAdapter implements ObserverOnSolving, ObserverOnDecisions,
        ObserverOnAssignments, ObserverOnConflicts, ObserverOnRuns, ObserverOnSolution {

    /**
     * The adapted Universe listener.
     */
    private final IUniverseSearchListener adaptee;

    /**
     * The solver that is being listened.
     */
    private final JUniverseAceProblemAdapter solver;

    /**
     * The current decision level in the solver.
     */
    private int currentLevel;

    /**
     * Creates a new AceSearchListenerAdapter.
     *
     * @param adaptee The Universe listener to adapt.
     * @param solver The solver that is being listened.
     */
    public AceSearchListenerAdapter(IUniverseSearchListener adaptee,
            JUniverseAceProblemAdapter solver) {
        this.adaptee = adaptee;
        this.solver = solver;
    }

    /**
     * Gives the adapted Universe listener.
     *
     * @return The adapted Universe listener.
     */
    public IUniverseSearchListener getAdaptee() {
        return adaptee;
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
     * @see
     * interfaces.Observers.ObserverOnDecisions#beforePositiveDecision(variables.Variable,
     * int)
     */
    @Override
    public void beforePositiveDecision(Variable x, int a) {
        currentLevel++;
        adaptee.onPositiveDecision(new JUniverseVariableAceAdapter(x), BigInteger.valueOf(a));
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
        currentLevel++;
        adaptee.onNegativeDecision(new JUniverseVariableAceAdapter(x), BigInteger.valueOf(a));
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
     * @see interfaces.Observers.ObserverOnRuns#afterRun()
     */
    @Override
    public void afterRun() {
        adaptee.onRestart();
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
     * @see interfaces.Observers.ObserverOnSolving#afterSolving()
     */
    @Override
    public void afterSolving() {
        adaptee.end(solver.getResult());
    }

}
