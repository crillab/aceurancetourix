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

import fr.univartois.cril.juniverse.core.problem.IUniverseDomain;
import fr.univartois.cril.juniverse.core.problem.IUniverseVariable;
import variables.Variable;


/**
 * The JUniverseVariableAceAdapter
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class JUniverseVariableAceAdapter implements IUniverseVariable {

    private Variable x;
    /**
     * 
     * Creates a new JUniverseVariableAceAdapter.
     * @param x The ACE Variable
     */
    public JUniverseVariableAceAdapter(Variable x) {
        this.x=x;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseVariable#getName()
     */
    @Override
    public String getName() {
         return x.id();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseVariable#getId()
     */
    @Override
    public int getId() {
        return x.num;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseVariable#getDomain()
     */
    @Override
    public IUniverseDomain getDomain() {
        return new JUniverseAceDomainAdapter(x.dom);
    }

}

