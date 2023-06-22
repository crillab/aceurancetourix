/**
 * This file is a part of the {@code fr.univartois.cril.aceurancetourix} package.
 *
 * It contains the type JUniverseAceConstraintAdapter.
 *
 * (c) 2023 Romain Wallon - aceurancetourix.
 * All rights reserved.
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
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class JUniverseAceConstraintAdapter implements IUniverseConstraint {

    private final Constraint constraint;

    /**
     * Creates a new JUniverseAceConstraintAdapter.
     * @param constraint
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
        return Arrays.stream(constraint.scp).map(JUniverseVariableAceAdapter::new).collect(Collectors.toList());
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

