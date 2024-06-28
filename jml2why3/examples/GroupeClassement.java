import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

class VoeuClasse {

    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;

    //@ public invariant 1 <= rang;

    //@ requires 1 <= rang;
    public /*@ pure @*/ VoeuClasse(
            final int rang,
            final boolean estBoursier,
            final boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }

    /*@ ensures \result == (this.rang == other.rang && this.estBoursier == other.estBoursier && this.estResident == other.estResident);
        public pure model boolean equals(final VoeuClasse other); @*/
}

public class GroupeClassement {

    /*le code identifiant le groupe de classement dans la base de données
        Remarque: un même groupe de classement peut être commun à plusieurs formations
     */
    public final int C_GP_COD;

    /* le taux minimum de boursiers dans ce groupe d'appel
        (nombre min de boursiers pour 100 candidats) */
    public final int tauxMinBoursiersPourcents;

    /* le taux minimum de candidats du secteur dans ce groupe d'appel
        (nombre min de candidats du secteur pour 100 candidats) */
    public final int tauxMinDuSecteurPourcents;

    /*@ invariant 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
        invariant 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100; @*/

    /*@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
        requires 0 <= tauxMinResidentsPourcents && tauxMinResidentsPourcents <= 100; @*/
    public /*@ pure @*/ GroupeClassement(
            final int C_GP_COD,
            final int tauxMinBoursiersPourcents,
            final int tauxMinResidentsPourcents) {
        this.C_GP_COD = C_GP_COD;
        this.tauxMinBoursiersPourcents = tauxMinBoursiersPourcents;
        this.tauxMinDuSecteurPourcents = tauxMinResidentsPourcents;
    }

    //@ requires voeuxClasses.size() * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rang, rangAppel
    //@ requires_redundantly voeuxClasses.size() < 21_474_836;
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.size(); voeuxClasses.get(i) != null);
    public LinkedList<VoeuClasse> calculerOrdreAppel(final LinkedList<VoeuClasse> voeuxClasses) {
        final Queue<VoeuClasse> BR = new LinkedList<>(), BnR = new LinkedList<>(), nBR = new LinkedList<>(), nBnR = new LinkedList<>();

        //@ loop_invariant \invariant_for(BR) && \invariant_for(BnR) && \invariant_for(nBR) && \invariant_for (nBnR);
        //@ loop_invariant (\forall int j; 0 <= j && j < voeuxClasses.size(); voeuxClasses.get(j) != null);
        //@ loop_invariant 0 <= i && i <= voeuxClasses.size();
        //@ loop_invariant BR.size() + BnR.size() + nBR.size() + nBnR.size() == i;
        //@ loop_invariant (\forall int j; 0 <= j && j < BR.size();   BR._get(j).estBoursier && BR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < BnR.size();  BnR._get(j).estBoursier && !BnR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBR.size();  !nBR._get(j).estBoursier && nBR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBnR.size(); !nBnR._get(j).estBoursier && !nBnR._get(j).estResident);
        //@ loop_modifies BR.content, BnR.content, nBR.content, nBnR.content;
        for (int i = 0; i < voeuxClasses.size(); i++) {
            final VoeuClasse voe = voeuxClasses.get(i);
            if (voe.estBoursier) {
                if (voe.estResident)
                    BR.add(voe);
                else
                    BnR.add(voe);
            } else {
                if (voe.estResident)
                    nBR.add(voe);
                else
                    nBnR.add(voe);
            }
        }

        final int nbBoursiersTotal = BR.size() + BnR.size();
        final int nbResidentsTotal = BR.size() + nBR.size();

        final LinkedList<VoeuClasse> ordreAppel = new LinkedList<>();

        //@ loop_invariant nbAppeles == ordreAppel.size();
        //@ loop_invariant \invariant_for(BR) && \invariant_for(BnR) && \invariant_for(nBR) && \invariant_for(nBnR);
        //@ loop_invariant 0 <= ordreAppel.size() && ordreAppel.size() <= voeuxClasses.size();
        //@ loop_invariant 0 <= BR.size() + BnR.size() && BR.size() + BnR.size() <= nbBoursiersTotal;
        //@ loop_invariant 0 <= BR.size() + nBR.size() && BR.size() + nBR.size() <= nbResidentsTotal;
        //@ loop_invariant ordreAppel.size() + BR.size() + BnR.size() + nBR.size() + nBnR.size() == voeuxClasses.size();

        //@ loop_invariant (\forall int i; 0 <= i && i < BR.size();   BR._get(i).estBoursier && BR._get(i).estResident);
        //@ loop_invariant (\forall int i; 0 <= i && i < BnR.size();  BnR._get(i).estBoursier && !BnR._get(i).estResident);
        //@ loop_invariant (\forall int i; 0 <= i && i < nBR.size();  !nBR._get(i).estBoursier && nBR._get(i).estResident);
        //@ loop_invariant (\forall int i; 0 <= i && i < nBnR.size(); !nBnR._get(i).estBoursier && !nBnR._get(i).estResident);

        //@ loop_invariant (\forall int i; 0 <= i && i < ordreAppel.size(); ordreAppel.get(i) != null);

        //@ loop_modifies ordreAppel.content, BR.content, BnR.content, nBR.content, nBnR.content;
        // while (ordreAppel.size() < voeuxClasses.size()) {
        for (int nbAppeles = 0; nbAppeles < voeuxClasses.size(); nbAppeles++) {

            final int nbBoursierRestants = BR.size() + BnR.size();
            final int nbResidentsRestants = BR.size() + nBR.size();
            final int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            final int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            final boolean contrainteTauxBoursier = 0 < nbBoursierRestants
                && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + ordreAppel.size()));

            //@ assert contrainteTauxBoursier ==> 0 < BR.content.theSize || 0 < BnR.content.theSize;

            final boolean contrainteTauxResident = 0 < nbResidentsRestants
                && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + ordreAppel.size()));

            //@ assert contrainteTauxResident ==> 0 < BR.content.theSize || 0 < nBR.content.theSize;

            /*@ nullable @*/ VoeuClasse meilleur = null;
            if (!BR.isEmpty()) {
                meilleur = BR.peek();
            }
            if (!nBR.isEmpty() && !contrainteTauxBoursier && (meilleur == null || meilleur.rang < nBR.peek().rang)) {
                meilleur = nBR.peek();
            }
            if (!BnR.isEmpty() && !contrainteTauxResident && (meilleur == null || meilleur.rang < BnR.peek().rang)) {
                meilleur = BnR.peek();
            }
            if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleur == null || meilleur.rang < nBnR.peek().rang)) {
                meilleur = nBnR.peek();
            }
            if (meilleur == null) {
                //@ assert 0 < BnR.size();
                meilleur = BnR.peek();
            }

            /*@ assert (0 < BR.size() && meilleur.equals(BR._get(0))) ||
                       (0 < BnR.size() && meilleur.equals(BnR._get(0))) ||
                       (0 < nBR.size() && meilleur.equals(nBR._get(0))) ||
                       (0 < nBnR.size() && meilleur.equals(nBnR._get(0))); @*/

            if (meilleur.estBoursier) {
                if (meilleur.estResident) {
                    //@ assert 0 < BR.size();
                    BR.poll();
                } else {
                    //@ assert 0 < BnR.size();
                    BnR.poll();
                }
            } else {
                if (meilleur.estResident) {
                    //@ assert 0 < nBR.size();
                    nBR.poll();
                } else {
                    //@ assert 0 < nBnR.size();
                    nBnR.poll();
                }
            }

            ordreAppel.add(meilleur);
        }

        return ordreAppel;
    }
}
