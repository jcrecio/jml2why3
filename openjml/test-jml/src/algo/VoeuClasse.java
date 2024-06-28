package algo;

public class VoeuClasse implements Comparable<VoeuClasse> {

    /* les différents types de candidats */
    public enum TypeCandidat {
        BoursierDuSecteur,
        BoursierHorsSecteur,
        NonBoursierDuSecteur,
        NonBoursierHorsSecteur
    };

    /* le type du candidat */
    public final TypeCandidat typeCandidat;

    /* code identifiant le candidat dans la base de données */
    public final int G_CN_COD;

    /* le rang du voeu transmis par la commission de classement des voeux */
    public final int rang;

    /* le rang du voeu dans l'ordre d'appel, caculé par l'algorithme */
    public int rangAppel = 0;

    public VoeuClasse(
            int G_CN_COD,
            int rang,
            boolean estBoursier,
            boolean estDuSecteur) {
        this.G_CN_COD = G_CN_COD;
        this.rang = rang;
        this.typeCandidat
                = estBoursier
                        ? (estDuSecteur ? TypeCandidat.BoursierDuSecteur : TypeCandidat.BoursierHorsSecteur)
                        : (estDuSecteur ? TypeCandidat.NonBoursierDuSecteur : TypeCandidat.NonBoursierHorsSecteur);
    }

    public boolean estBoursier() {
        return typeCandidat == TypeCandidat.BoursierDuSecteur
                || typeCandidat == TypeCandidat.BoursierHorsSecteur;
    }

    public boolean estDuSecteur() {
        return typeCandidat == TypeCandidat.BoursierDuSecteur
                || typeCandidat == TypeCandidat.NonBoursierDuSecteur;
    }

    /* comparateur permettant de trier les voeux par ordre du groupe de classement */
    @Override
    public int compareTo(VoeuClasse o) {
        return rang - o.rang;
    }

    @Override
    public String toString() {
        return "VoeuClasse [typeCandidat=" + typeCandidat + ", G_CN_COD=" + G_CN_COD + ", rang=" + rang + "]";
    }

}
