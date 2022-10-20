module fr.univartois.cril.assurancetourix{
    requires ACE;
    requires xcsp3.tools;
    opens fr.univartois.cril.assurancetourix to ACE,xcsp3.tools;
    requires transitive fr.univartois.cril.juniverse;
    exports fr.univartois.cril.assurancetourix;
}