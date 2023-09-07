/**
 * The {@code fr.univartois.cril.aceurancetourix} module provides the JUniverse adapter
 * for the ACE CP solver.
 *
 * @provides fr.univartois.cril.juniverse.utils.IUniverseSolverFactory
 *
 * @author Thibault Falque
 * @author Romain Wallon
 *
 * @version 0.1.0
 */
module fr.univartois.cril.aceurancetourix {

    // Exported packages.

    exports fr.univartois.cril.aceurancetourix;

    exports fr.univartois.cril.aceurancetourix.reader;

    // Required standard Java module.

    requires java.xml;

    // Required modules for solving.

    requires ace;

    requires transitive fr.univartois.cril.juniverse;

    requires xcsp3.tools;

    // Allowing XCSP3 tools to inject data when parsing.

    opens fr.univartois.cril.aceurancetourix to xcsp3.tools;

    // Declaring the SolverFactory as provided services.

    provides fr.univartois.cril.juniverse.utils.IUniverseSolverFactory with
        fr.univartois.cril.aceurancetourix.AceSolverFactory,
        fr.univartois.cril.aceurancetourix.AceSolverFactorySingleSolution,
        fr.univartois.cril.aceurancetourix.PreprocAceSolverFactory;

}
