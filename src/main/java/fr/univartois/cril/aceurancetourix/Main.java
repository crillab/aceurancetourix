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

import java.io.IOException;
import java.math.BigInteger;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;

import fr.univartois.cril.aceurancetourix.reader.XCSP3Reader;
import fr.univartois.cril.juniverse.core.UniverseAssumption;
import fr.univartois.cril.juniverse.core.UniverseContradictionException;

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
        var factory = new AceSolverFactorySingleSolution();
        JUniverseAceProblemAdapter solver = (JUniverseAceProblemAdapter) factory.createCspSolver();
        solver.getHead().getBuilder().getOptionsGeneralBuilder().setExceptionsVisible(true);
        solver.getHead().getBuilder().getOptionsGeneralBuilder().setEnableAnnotations(true);
        solver.getHead().getBuilder().getOptionsGeneralBuilder().setVerbose(1);
//        XCSP3Reader reader = new XCSP3Reader(solver);
//        try {
//            reader.parseInstance(args[0]);
//        } catch (UniverseContradictionException | IOException e) {
//            e.printStackTrace();
//        }
        solver.loadInstance(args[0]);
        //solver.setBounds(BigInteger.valueOf(74), BigInteger.valueOf(862));
        System.out.println(solver.solve());
        solver.reset();
        solver.setUpperBound(BigInteger.valueOf(148));
        System.out.println(solver.solve());
        
    }

}
