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

package fr.univartois.cril.assurancetourix;

import static org.xcsp.common.Types.TypeFramework.COP;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BiFunction;
import java.util.function.Consumer;

import org.xcsp.common.IVar.Var;
import org.xcsp.common.Types.TypeFramework;
import org.xcsp.modeler.entities.VarEntities.VarArray;

import fr.univartois.cril.juniverse.core.UniverseSolverResult;
import interfaces.Observers.ObserverOnConstruction;
import main.Head;
import problem.Problem;
import problem.XCSP3;
import solver.Solver.Stopping;

/**
 * The AceHead
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class AceHead extends Head {

    AceXCSP3 xcsp3;
    private volatile boolean interrupted;

    public AceHead() {
        xcsp3 = new AceXCSP3(this);
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
    
    public void interruptSearch() {
        interrupted=true;
    }

    public UniverseSolverResult isSatisfiable() {
        interrupted=false;
        structureSharing.clear();
        problem = buildProblem(0);
        structureSharing.clear();
        if (control.solving.enablePrepro || control.solving.enableSearch) {
            solver = buildSolver(problem);
            solver.solve();
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

    @Override
    public Problem buildProblem(int i) {
        problem = new Problem(xcsp3, "", "", "", false, new String[0], this);
        problem.priorityArrays = new VarArray[0];
        for (ObserverOnConstruction obs : observersConstruction)
            obs.afterProblemConstruction(this.problem.variables.length);
        return problem;
    }
    
    static class AceXCSP3 extends XCSP3 {

        private Head head;

        private List<Consumer<Problem>> constraintsToAdd;

        private Map<String, BiFunction<Problem, String, Var>> variablesToAdd;

        private Map<String, Var> mapping;

        /**
         * Creates a new AceXCSP3.
         */
        public AceXCSP3(Head head) {
            this.constraintsToAdd = new ArrayList<>();
            this.variablesToAdd = new HashMap<>();
            this.mapping = new HashMap<>();
            this.head = head;
        }

        @Override
        public void data() {

        }

        @Override
        public void model() {
            variablesToAdd.forEach((s, f) -> mapping.put(s, f.apply(head.problem, s)));
            constraintsToAdd.forEach(c -> c.accept(head.problem));
            endVariables();
            endConstraints();
            endInstance();
        }

        public void addConstraintsToAdd(Consumer<Problem> c) {
            this.constraintsToAdd.add(c);
        }

        public void addVariableToAdd(String k, BiFunction<Problem, String, Var> bf) {
            variablesToAdd.put(k, bf);
        }

        public Var getVariable(String k) {
            return mapping.get(k);
        }
    }

}
