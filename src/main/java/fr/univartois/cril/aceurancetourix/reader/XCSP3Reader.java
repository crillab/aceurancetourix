/**
 * Sat4j-CSP, a CSP solver based on the Sat4j platform.
 * Copyright (c) 2021-2022 - Exakis Nelite, Univ Artois & CNRS.
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

package fr.univartois.cril.aceurancetourix.reader;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.Reader;

import javax.xml.parsers.DocumentBuilderFactory;

import fr.univartois.cril.juniverse.core.UniverseContradictionException;
import fr.univartois.cril.juniverse.csp.IUniverseCSPSolver;

/**
 * The XCSP3Reader is a {@link Reader} that allows to feed an XCSP3 instance to
 * an {@link ICSPSolver}.
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
public class XCSP3Reader {
    /**
     * The solver to which the read constraints will be added.
     */
    private IUniverseCSPSolver solver;

    /**
     * The callback that will be notified while reading the input instance.
     */
    private XCSPXCallback callback;

    /**
     * Creates a new XCSP3Reader.
     *
     * @param solver The solver to which the read constraints will be added.
     */
    public XCSP3Reader(IUniverseCSPSolver solver) {
        this.solver = solver;
        this.callback = new XCSPXCallback(solver);
    }

    /*
     * (non-Javadoc)
     *
     * @see org.sat4j.reader.Reader#parseInstance(java.io.InputStream)
     */
    public void parseInstance(InputStream in)
            throws UniverseContradictionException, IOException {
        try {
            var document = DocumentBuilderFactory.newInstance().newDocumentBuilder().parse(in);
            callback.loadInstance(document);
        } catch (UniverseContradictionException e) {
            e.printStackTrace();
            throw new UniverseContradictionException(e);

        } catch (UnsupportedOperationException | IOException e) {
            e.printStackTrace();
            throw e;

        } catch (Exception e) {
            e.printStackTrace();
            throw new IOException(e);
        }
        
    }
    
    public void parseInstance(String filename) throws UniverseContradictionException, IOException {
    	try {
			parseInstance(new FileInputStream(filename));
		} catch (UniverseContradictionException e) {
            throw new UniverseContradictionException(e);
        } catch (UnsupportedOperationException | IOException e) {
            e.printStackTrace();
            throw e;
        } catch (Exception e) {
            e.printStackTrace();
            throw new IOException(e);
        }
    }



}
