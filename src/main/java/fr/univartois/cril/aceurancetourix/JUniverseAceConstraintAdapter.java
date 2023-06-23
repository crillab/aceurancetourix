/**
 * Aceurancetourix, the JUniverse adapter for ACE.
 * Copyright (c) 2022-2023 - Univ Artois, CNRS & Exakis Nelite.
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

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import constraints.Constraint;
import fr.univartois.cril.juniverse.core.problem.IUniverseConstraint;
import fr.univartois.cril.juniverse.core.problem.IUniverseVariable;

/**
 * The JUniverseAceConstraintAdapter
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
class JUniverseAceConstraintAdapter implements IUniverseConstraint {

    /**
     * The adapted constraint.
     */
    private final Constraint constraint;

    /**
     * Creates a new JUniverseAceConstraintAdapter.
     *
     * @param constraint The constraint to adapt.
     */
    public JUniverseAceConstraintAdapter(Constraint constraint) {
        this.constraint = constraint;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseConstraint#scope()
     */
    @Override
    public List<IUniverseVariable> scope() {
        return Arrays.stream(constraint.scp)
                .map(JUniverseVariableAceAdapter::new)
                .collect(Collectors.toList());
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseConstraint#getScore()
     */
    @Override
    public double getScore() {
        return constraint.wdeg();
    }

}
