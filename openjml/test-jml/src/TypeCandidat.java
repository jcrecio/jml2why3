
enum TypeCandidat {
    BoursierDuSecteur,
    BoursierHorsSecteur,
    NonBoursierDuSecteur,
    NonBoursierHorsSecteur;
    /*@ pure @*/ boolean estBoursier() {
        return this == TypeCandidat.BoursierDuSecteur
            || this == TypeCandidat.BoursierHorsSecteur;
    }
    /*@ pure @*/ boolean estDuSecteur() {
        return this == TypeCandidat.BoursierDuSecteur
            || this == TypeCandidat.NonBoursierDuSecteur;
    }
}
