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

import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;
import fr.univartois.cril.juniverse.pb.IUniversePseudoBooleanSolver;
import fr.univartois.cril.juniverse.sat.IUniverseSatSolver;
import fr.univartois.cril.juniverse.utils.IUniverseSolverFactory;


/**
 * The AceSolverFactorySingleSolution
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class AceSolverFactorySingleSolution implements IUniverseSolverFactory {

    /**
     * Creates a new AceSolverFactorySingleSolution.
     */
    public AceSolverFactorySingleSolution() {
        // TODO Auto-generated constructor stub
    }

    /**
     * Creates a {@link IUniverseCSPSolver} implemented using an instance of ACE in its
     * default configuration.
     *
     * @return The created solver.
     */
    public static IUniverseCSPSolver newDefault() {
        var s = new JUniverseAceProblemAdapter();
        s.getBuilder().getOptionsGeneralBuilder().setNoPrintColors(true);
        s.getBuilder().getOptionsGeneralBuilder().setSolLimit(1);
        return s;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.utils.ISolverFactory#createSatSolver()
     */
    @Override
    public IUniverseSatSolver createSatSolver() {
        return newDefault();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.utils.ISolverFactory#createPseudoBooleanSolver()
     */
    @Override
    public IUniversePseudoBooleanSolver createPseudoBooleanSolver() {
        return newDefault();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.utils.ISolverFactory#createCspSolver()
     */
    @Override
    public IUniverseCSPSolver createCspSolver() {
        return newDefault();
    }

    /*
     * (non-Javadoc)
     *
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return "Aceurancetourix (single solution)";
    }

}

