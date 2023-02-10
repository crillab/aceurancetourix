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

import java.math.BigInteger;
import java.util.List;

import fr.univartois.cril.juniverse.core.UniverseAssumption;

/**
 * The Main
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class Main {

    /**
     * Creates a new Main.
     */
    public Main() {
        // TODO Auto-generated constructor stub
    }
    
    public static void main(String[] args) {
        var factory = new AceSolverFactory();
        JUniverseAceProblemAdapter solver=(JUniverseAceProblemAdapter)factory.createCspSolver();
        System.out.println(solver.solve(args[0]));
        solver.getHead().solver.solutions.displayFinalResults();
        
    }

}

