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

import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;
import fr.univartois.cril.juniverse.pb.IUniversePseudoBooleanSolver;
import fr.univartois.cril.juniverse.sat.IUniverseSatSolver;
import fr.univartois.cril.juniverse.utils.ISolverFactory;

/**
 * The AceSolverFactory
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class AceSolverFactory implements ISolverFactory {

    /**
     * Creates a new AceSolverFactory.
     */
    public AceSolverFactory() {
    }
    
    public static IUniverseCSPSolver newDefault(){
        return new JUniverseAceProblemAdapter();
    }

    @Override
    public IUniverseSatSolver createSatSolver() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IUniversePseudoBooleanSolver createPseudoBooleanSolver() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public IUniverseCSPSolver createCspSolver() {
        return newDefault();
    }
    
    
}

