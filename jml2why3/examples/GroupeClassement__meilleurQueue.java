import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

// It takes a while to verify, don’t give up:
// java -jar ~/source/openjml/OpenJML/OpenJML/tempjars/openjml.jar -command=esc examples/GroupeClassement__meilleurQueue.java
// 643.56s user 0.83s system 102% cpu 10:29.71 total

class VoeuClasse {

    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;
    public int rangAppel = 0;

    public VoeuClasse(
            int rang,
            boolean estBoursier,
            boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }
}

class GroupeClassement {

    //@ requires voeuxClasses.length * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rangAppel
    //@ requires_redundantly voeuxClasses.length < 21_474_836;
    //@ requires \nonnullelements(voeuxClasses);
    //@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    //@ requires 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100;
    //@ ensures \nonnullelements(\result);
    public VoeuClasse[] calculerOrdreAppel(final VoeuClasse[] voeuxClasses, final int tauxMinBoursiersPourcents, final int tauxMinDuSecteurPourcents) {
        Queue<VoeuClasse>
            BR = new LinkedList<>(),
            BnR = new LinkedList<>(),
            nBR = new LinkedList<>(),
            nBnR = new LinkedList<>();

        //@ loop_modifies BR.content, BnR.content, nBR.content, nBnR.content;
        //@ loop_invariant \invariant_for(BR); maintaining \invariant_for(BnR); maintaining \invariant_for(nBR); maintaining \invariant_for(nBnR);
        //@ loop_invariant BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == i;
        //@ loop_invariant 0 <= i && i <= voeuxClasses.length;
        for (int i = 0; i <= voeuxClasses.length - 1; i++) {
            VoeuClasse voe = voeuxClasses[i];
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

        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        int nbBoursiersTotal = BR.size() + BnR.size();
        int nbResidentsTotal = BR.size() + nBR.size();

        //@ loop_modifies nbAppeles;
        //@ loop_modifies BR.content, BnR.content, nBR.content, nBnR.content, ordreAppel[*];
        //@ loop_invariant 0 <= nbAppeles && nbAppeles <= ordreAppel.length;
        //@ loop_invariant \invariant_for(BR); maintaining \invariant_for(BnR); maintaining \invariant_for(nBR); maintaining \invariant_for(nBnR);
        //@ loop_invariant (\forall int i; 0 <= i && i < ordreAppel.length; ordreAppel[i] == null <==> nbAppeles <= i);
        //@ loop_invariant 0 <= BR.content.theSize + BnR.content.theSize && BR.content.theSize + BnR.content.theSize <= nbBoursiersTotal;
        //@ loop_invariant 0 <= BR.content.theSize + nBR.content.theSize && BR.content.theSize + nBR.content.theSize <= nbResidentsTotal;
        //@ loop_invariant nbAppeles + BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == voeuxClasses.length;
        for (int nbAppeles = 0; nbAppeles < ordreAppel.length; nbAppeles++) {

            int nbBoursierRestants = BR.size() + BnR.size();
            int nbResidentsRestants = BR.size() + nBR.size();
            int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            boolean contrainteTauxBoursier = 0 < nbBoursierRestants
                && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxBoursier ==> 0 < BR.content.theSize || 0 < BnR.content.theSize;

            boolean contrainteTauxResident = 0 < nbResidentsRestants
                && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxResident ==> 0 < BR.content.theSize || 0 < nBR.content.theSize;

            //@ assert 0 < BR.content.theSize || 0 < BnR.content.theSize || 0 < nBR.content.theSize || 0 < nBnR.content.theSize;

            /*@ nullable @*/ Queue<VoeuClasse> meilleurQueue = null;
            if (!BR.isEmpty())
                meilleurQueue = BR;
            if (!BnR.isEmpty() && !contrainteTauxResident && (meilleurQueue == null || BnR.peek().rang < meilleurQueue.peek().rang))
                meilleurQueue = BnR;
            if (!nBR.isEmpty() && !contrainteTauxBoursier && (meilleurQueue == null || nBR.peek().rang < meilleurQueue.peek().rang))
                meilleurQueue = nBR;
            if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleurQueue == null || nBnR.peek().rang < meilleurQueue.peek().rang))
                meilleurQueue = nBnR;

            if (meilleurQueue == null) {
                //@ assert 0 < BnR.content.theSize;
                meilleurQueue = BnR;
            }

            VoeuClasse meilleur = meilleurQueue.poll();
            //@ assert meilleur != null;
            ordreAppel[nbAppeles] = meilleur;
        }

        int rangAppel = 1;
        //@ maintaining rangAppel == \count+1;
        // loop_modifies ordreAppel[0..ordreAppel.length-1].rangAppel;
        for (VoeuClasse voe: ordreAppel)
            voe.rangAppel = rangAppel++;

        return ordreAppel;
    }
}

public class GroupeClassement__meilleurQueue {}
