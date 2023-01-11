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

import static org.xcsp.common.Types.TypeFramework.COP;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.BiFunction;
import java.util.function.Consumer;

import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.entities.VarEntities.VarArray;

import fr.univartois.cril.juniverse.core.UniverseSolverResult;
import interfaces.Observers.ObserverOnConstruction;
import main.Head;
import problem.Problem;
import problem.XCSP3;
import solver.AceBuilder;
import solver.Assumption;
import solver.Solver.Stopping;
import variables.Variable;

/**
 * The AceHead is a specialization of ACE's {@link Head} that allows to interact with the
 * solver, and especially to add constraints into it using an API rather than an input
 * XCSP3 file.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class AceHead extends Head {

    /**
     * The builder used to initialize the structures of ACE.
     */
    private final AceBuilder builder;

    /**
     * A custom XCSP3 instance, simulating the parsing of an XCSP3 file when adding
     * constraints.
     */
    AceXCSP3 xcsp3;

    /**
     * Boolean indicating if the solver must be interrupted or not.
     */
    private volatile boolean interrupted;

    /**
     * Boolean indicating if the problem is built or not.
     */
    private boolean problemBuilt;

    /**
     * Boolean indicating if the solver is built or not.
     */
    private boolean solverBuilt;

    /**
     * Creates a new AceHead.
     */
    public AceHead() {
        xcsp3 = new AceXCSP3(this);
        this.builder = new AceBuilder(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see main.Head#getBuilder()
     */
    @Override
    public AceBuilder getBuilder() {
        return builder;
    }

    /*
     * (non-Javadoc)
     *
     * @see main.Head#isTimeExpiredForCurrentInstance()
     */
    @Override
    public boolean isTimeExpiredForCurrentInstance() {
        return super.isTimeExpiredForCurrentInstance() || interrupted;

    }

    /**
     * Interrupts the solver.
     */
    public void interruptSearch() {
        interrupted = true;
    }

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver.
     * 
     * @return A UniverseSolverResult indicating the satisfiability of the problem.
     */
    public UniverseSolverResult isSatisfiable() {
        return isSatisfiable(List.of());
    }

    /**
     * Check the satisfiability of the set of constraints contained inside the
     * solver using the specified assumption.
     * 
     * @param assumpts The assumptions to consider when solving.
     * @return The outcome of the search conducted by the solver.
     */
    public UniverseSolverResult isSatisfiable(List<Assumption> assumpts) {
        interrupted = false;
        if (!problemBuilt) {
            structureSharing.clear();
            problem = buildProblem(0);
            structureSharing.clear();
        }
        if (control.solving.enablePrepro || control.solving.enableSearch) {
            if (!solverBuilt) {
                solver = buildSolver(problem);
                solverBuilt = true;
            }
            solver.solve(assumpts);
            boolean fullExploration = solver.stopping == Stopping.FULL_EXPLORATION;
            TypeFramework framework = solver.problem.framework;
            if (fullExploration) {
                if (solver.solutions.found == 0) {
                    return UniverseSolverResult.UNSATISFIABLE;
                } else if (framework == COP) {
                    return UniverseSolverResult.OPTIMUM_FOUND;
                } else {
                    return UniverseSolverResult.SATISFIABLE;
                }
            } else if (solver.solutions.found == 0) {
                return UniverseSolverResult.UNKNOWN;
            } else {
                return UniverseSolverResult.SATISFIABLE;
            }
        }
        return UniverseSolverResult.UNKNOWN;
    }

    /*
     * (non-Javadoc)
     *
     * @see main.Head#buildProblem(int)
     */
    @Override
    public Problem buildProblem(int i) {
        if (!problemBuilt) {
            problem = new Problem(xcsp3, "", "", "", false, new String[0], this);
            problem.priorityArrays = new VarArray[0];
            for (ObserverOnConstruction obs : observersConstruction)
                obs.afterProblemConstruction(this.problem.variables.length);
            problemBuilt = true;
        }
        return problem;
    }

    /**
     * A custom {@link XCSP3} specialization, simulating the parsing of an XCSP3 file when
     * adding constraints.
     */
    static class AceXCSP3 extends XCSP3 {

        /**
         * ACE's Head.
         */
        private Head head;

        /**
         * The variables to be added to the solver.
         */
        private Map<String, BiFunction<Problem, String, Variable>> variablesToAdd;

        /**
         * The names of the variables that have been added.
         * It allows to preserve their order.
         */
        private List<String> variables;

        /**
         * The mapping associating the name of a variable to ACE's representation of this
         * variable.
         */
        private Map<String, Variable> mapping;

        /**
         * The constraint to be added to the solver.
         */
        private List<Consumer<Problem>> constraintsToAdd;

        /**
         * Creates a new AceXCSP3.
         * 
         * @param head ACE's Head.
         */
        public AceXCSP3(Head head) {
            this.constraintsToAdd = new ArrayList<>();
            this.variables = new ArrayList<>();
            this.variablesToAdd = new HashMap<>();
            this.mapping = new HashMap<>();
            this.head = head;
        }

        /*
         * (non-Javadoc)
         *
         * @see problem.XCSP3#data()
         */
        @Override
        public void data() {
            // Nothing to do here.
        }

        /*
         * (non-Javadoc)
         *
         * @see problem.XCSP3#model()
         */
        @Override
        public void model() {
            variables.forEach((v) -> {
                Variable variable = variablesToAdd.get(v).apply(head.problem, v);
                mapping.put(v, variable);
            });
            constraintsToAdd.forEach(c -> c.accept(head.problem));
            endVariables();
            endConstraints();
            endInstance();
        }

        /**
         * Adds a variable to the solver.
         * 
         * @param name The name of the variable.
         * @param v The function to invoke to add the variable.
         */
        public void addVariableToAdd(String name, BiFunction<Problem, String, Variable> v) {
            variablesToAdd.put(name, v);
            variables.add(name);
        }

        /**
         * Gives the variable with the given name.
         *
         * @param name The name of the variable.
         *
         * @return The variable with the given name.
         */
        public Variable getVariable(String name) {
            return Objects.requireNonNull(mapping.get(name));
        }

        /**
         * Adds a constraint to the solver.
         *
         * @param c The function to invoke to add the constraint.
         */
        public void addConstraintsToAdd(Consumer<Problem> c) {
            this.constraintsToAdd.add(c);
        }
    }

}
