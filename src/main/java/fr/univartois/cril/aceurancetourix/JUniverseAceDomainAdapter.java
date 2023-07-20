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
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.xcsp.common.Range;

import fr.univartois.cril.juniverse.core.problem.IUniverseDomain;
import variables.Domain;

/**
 * The JUniverseAceDomainAdapter
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class JUniverseAceDomainAdapter implements IUniverseDomain {

    private Domain dom;


    /**
     * Creates a new JUniverseAceDomainAdapter.
     * @param dom The ACE domain
     */
    public JUniverseAceDomainAdapter(Domain dom) {
        this.dom = dom;
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseDomain#min()
     */
    @Override
    public BigInteger min() {
        return BigInteger.valueOf(this.dom.firstValue());
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseDomain#max()
     */
    @Override
    public BigInteger max() {
        return BigInteger.valueOf(this.dom.lastValue());
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseDomain#size()
     */
    @Override
    public long size() {
        return this.dom.size();
    }

    /*
     * (non-Javadoc)
     *
     * @see fr.univartois.cril.juniverse.core.problem.IUniverseDomain#getValues()
     */
    @Override
    public List<BigInteger> getValues() {
        var ugly = this.dom.allValues();
        if (ugly instanceof Range) {
            var range = (Range) ugly;
            return range.stream().mapToObj(BigInteger::valueOf).collect(Collectors.toList());
        } else {
            var tab = (int[]) ugly;
            return IntStream.of(tab).mapToObj(BigInteger::valueOf).collect(Collectors.toList());
        }
    }

	@Override
	public long currentSize() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public List<BigInteger> getCurrentValues() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void keepValues(BigInteger min, BigInteger max) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void keepValues(List<BigInteger> values) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeValues(BigInteger min, BigInteger max) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void removeValues(List<BigInteger> values) {
		throw new UnsupportedOperationException();
	}

}
