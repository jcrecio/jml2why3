import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

class VoeuClasse {

    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;
    public int rangAppel = -1;

    //@ invariant 0 <= rang && rang <= Integer.MAX_VALUE;

    //@ requires 0 <= rang && rang <= Integer.MAX_VALUE;
    public VoeuClasse(
            final int rang,
            final boolean estBoursier,
            final boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }

    static void test() {
        VoeuClasse v = new VoeuClasse(0, true, true);
        v.rangAppel = 1;
    }
}

public class GroupeClassement__target {

    //@ requires voeuxClasses.length * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rangAppel
    //@ requires_redundantly voeuxClasses.length < 21_474_836;
    //@ requires \nonnullelements(voeuxClasses);
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.length; \invariant_for(voeuxClasses[i]));
    //@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    //@ requires 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100;
    //@ ensures \nonnullelements(\result);
    public VoeuClasse[] calculerOrdreAppel(final VoeuClasse[] voeuxClasses, final int tauxMinBoursiersPourcents, final int tauxMinDuSecteurPourcents) {
        final Queue<VoeuClasse> BR = new LinkedList<>(), BnR = new LinkedList<>(), nBR = new LinkedList<>(), nBnR = new LinkedList<>();

        //@ loop_invariant \invariant_for(BR); loop_invariant \invariant_for(BnR); loop_invariant \invariant_for(nBR); loop_invariant \invariant_for (nBnR);
        //@ loop_invariant BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == i;
        //@ loop_invariant 0 <= i && i <= voeuxClasses.length;
        //@ loop_invariant (\forall int j; 0 <= j && j < BR.content.theSize;   BR._get(j).estBoursier && BR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < BnR.content.theSize;  BnR._get(j).estBoursier && !BnR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBR.content.theSize;  !nBR._get(j).estBoursier && nBR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBnR.content.theSize; !nBnR._get(j).estBoursier && !nBnR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < voeuxClasses.length;  \invariant_for(voeuxClasses[j]));
        //@ loop_modifies BR.values, BnR.values, nBR.values, nBnR.values;
        //@ loop_modifies BR.content, BnR.content, nBR.content, nBnR.content;
        for (final int i = 0; i <= voeuxClasses.length - 1; i++) {
            final VoeuClasse voe = voeuxClasses[i];
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

        final VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        //@ loop_invariant \invariant_for(BR); maintaining \invariant_for(BnR); maintaining \invariant_for(nBR); maintaining \invariant_for(nBnR);
        //@ loop_invariant 0 <= nbAppeles && nbAppeles <= ordreAppel.length;
        //@ loop_invariant 0 <= BR.content.theSize + BnR.content.theSize && BR.content.theSize + BnR.content.theSize <= nbBoursiersTotal;
        //@ loop_invariant 0 <= BR.content.theSize + nBR.content.theSize && BR.content.theSize + nBR.content.theSize <= nbResidentsTotal;
        //@ loop_invariant nbAppeles + BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == voeuxClasses.length;
        //@ loop_invariant (\forall int j; 0 <= j && j < BR.content.theSize;   BR._get(j).estBoursier && BR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < BnR.content.theSize;  BnR._get(j).estBoursier && !BnR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBR.content.theSize;  !nBR._get(j).estBoursier && nBR._get(j).estResident);
        //@ loop_invariant (\forall int j; 0 <= j && j < nBnR.content.theSize; !nBnR._get(j).estBoursier && !nBnR._get(j).estResident);
        //@ loop_invariant (\forall int i; 0 <= i && i < ordreAppel.length; ordreAppel[i] == null <==> nbAppeles <= i);
        //@ loop_modifies nbAppeles, ordreAppel[*];
        //@ loop_modifies BR.content.theSize, BnR.content.theSize, nBR.content.theSize, nBnR.content.theSize;
        //@ loop_modifies BR.values, BnR.values, nBR.values, nBnR.values;
        for (final int nbAppeles = 0; nbAppeles < voeuxClasses.length; nbAppeles++) {

            final int nbBoursierRestants = BR.size() + BnR.size();
            final int nbResidentsRestants = BR.size() + nBR.size();
            final int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            final int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            final boolean contrainteTauxBoursier = 0 < nbBoursierRestants
                && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxBoursier ==> 0 < BR.content.theSize || 0 < BnR.content.theSize;

            final boolean contrainteTauxResident = 0 < nbResidentsRestants
                && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxResident ==> 0 < BR.content.theSize || 0 < nBR.content.theSize;

            // // Option 1: Choose best queue, poll best candidate from that
            // // -> Cannot be compiled to Why3 because requires mutating shared value (meilleurQueue.contents)

            //@ assert 0 < BR.content.theSize || 0 < BnR.content.theSize || 0 < nBR.content.theSize || 0 < nBnR.content.theSize;

            // /*@ nullable @*/ Queue<VoeuClasse> meilleurQueue = null;
            // if (!BR.isEmpty())
            //     meilleurQueue = BR;
            // if (!BnR.isEmpty() && !contrainteTauxResident && (meilleurQueue == null || BnR.peek().rang < meilleurQueue.peek().rang))
            //     meilleurQueue = BnR;
            // if (!nBR.isEmpty() && !contrainteTauxBoursier && (meilleurQueue == null || nBR.peek().rang < meilleurQueue.peek().rang))
            //     meilleurQueue = nBR;
            // if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleurQueue == null || nBnR.peek().rang < meilleurQueue.peek().rang))
            //     meilleurQueue = nBnR;

            // if (meilleurQueue == null) {
            //     //@ assert 0 < BnR.content.theSize;
            //     meilleurQueue = BnR;
            // }

            // VoeuClasse meilleur = meilleurQueue.poll();

            // // Option 2: Choose best candidate, select using a priority queue
            // // -> Not easy to convert to Why3 due to the missing specs for priority queues

            // Queue<VoeuClasse> eligibles = new PriorityQueue<>();
            // if (!BR.isEmpty())
            //     eligibles.add(BR.peek());
            // if (!nBR.isEmpty() && !contrainteTauxBoursier)
            //     eligibles.add(nBR.peek());
            // if (!BnR.isEmpty() && !contrainteTauxResident)
            //     eligibles.add(BnR.peek());
            // if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident)
            //     eligibles.add(nBnR.peek());

            // /*@ nullable @*/ VoeuClasse meilleur = null;
            // if (!eligibles.isEmpty())
            //     meilleur = eligibles.peek();
            // else {
            //     //@ assert 0 < BnR.content.theSize;
            //     meilleur = BnR.peek();
            // }

            // if (meilleur.estBoursier && meilleur.estResident)
            //     BR.poll();
            // else if (meilleur.estBoursier && !meilleur.estResident)
            //     BnR.poll();
            // else if (!meilleur.estBoursier && meilleur.estResident)
            //     nBR.poll();
            // else {
            //     assert (!meilleur.estBoursier && !meilleur.estResident);
            //     nBnR.poll();
            // }

            // Option 3: Choose and select best candidate directly
            // -> Easy translation to Why3

            /*@ nullable @*/ VoeuClasse meilleur = null;
            if (!BR.isEmpty())
                meilleur = BR.peek();
            if (!nBR.isEmpty() && !contrainteTauxBoursier && (meilleur == null || meilleur.rang < nBR.peek().rang))
                meilleur = nBR.peek();
            if (!BnR.isEmpty() && !contrainteTauxResident && (meilleur == null || meilleur.rang < BnR.peek().rang))
                meilleur = BnR.peek();
            if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleur == null || meilleur.rang < nBnR.peek().rang))
                meilleur = nBnR.peek();

            if (meilleur == null) {
                //@ assert 0 < BnR.content.theSize;
                meilleur = BnR.peek();
            }

            // //@ assert meilleur != null;
            // //@ assert meilleur.estBoursier && meilleur.estResident ==> 0 < BR.content.theSize;
            // //@ assert !meilleur.estBoursier && meilleur.estResident ==> 0 < nBR.content.theSize;
            // //@ assert meilleur.estBoursier && !meilleur.estResident ==> 0 < BnR.content.theSize;
            // //@ assert !meilleur.estBoursier && !meilleur.estResident ==> 0 < nBnR.content.theSize;

            // before:

            final VoeuClasse meilleur1 = meilleur;

            if (meilleur.estBoursier && meilleur.estResident) {
                BR.poll();
                // //@ assert BR.content.theSize == \old(BR.content.theSize, before) - 1;
            } else if (meilleur.estBoursier && !meilleur.estResident) {
                BnR.poll();
                // //@ assert BnR.content.theSize == \old(BnR.content.theSize, before) - 1;
            } else if (!meilleur.estBoursier && meilleur.estResident) {
                nBR.poll();
                // //@ assert nBR.content.theSize == \old(nBR.content.theSize, before) - 1;
            } else {
                //@ assert (!meilleur.estBoursier && !meilleur.estResident);
                nBnR.poll();
                // //@ assert nBnR.content.theSize == \old(nBnR.content.theSize, before) - 1;
            }

            // //@ assume BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == \old(BR, before).content.theSize + \old(BnR, before).content.theSize + \old(nBR, before).content.theSize + \old(nBnR, before).content.theSize - 1;

            // End select best candidate
            ordreAppel[nbAppeles] = meilleur;
        }

        int rangAppel = 1;
        //@ maintaining rangAppel == \count+1;
        // loop_modifies ordreAppel[0..ordreAppel.length-1].rangAppel;
        for (final int i=0; i<=ordreAppel.length; i++)
            ordreAppel[i].rangAppel = i;

        return ordreAppel;
    }
}
