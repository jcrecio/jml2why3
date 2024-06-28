import java.util.LinkedList;
import java.util.Queue;

public class OrdreAppel2 {

    static class VoeuClasse {

        public final int rang;
        public final boolean estBoursier;
        public final boolean estResident;
        public int rangAppel = -1;

        public VoeuClasse(int rang, boolean estBoursier, boolean estResident) {
            this.rang = rang;
            this.estBoursier = estBoursier;
            this.estResident = estResident;
        }
    }

    //@ requires voeuxClasses.length * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rangAppel
    //@ requires_redundantly voeuxClasses.length < 21_474_836;
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.length; voeuxClasses[i] != null);
    //@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    //@ requires 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100;
    public VoeuClasse[] ordreAppel(VoeuClasse[] voeuxClasses, int tauxMinBoursiersPourcents, int tauxMinDuSecteurPourcents) {

        Queue<VoeuClasse>
            BR = new LinkedList<>(),
            BnR = new LinkedList<>(),
            nBR = new LinkedList<>(),
            nBnR = new LinkedList<>();

        //@ maintaining 0 <= BR.content.theSize && 0 <= BnR.content.theSize && 0 <= nBR.content.theSize && 0 <= nBnR.content.theSize;
        //@ maintaining BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == \count;
        //@ maintaining 0 <= \count && \count <= voeuxClasses.length;
        //@ loop_modifies BR.values, BnR.values, nBR.values, nBnR.values;
        //@ loop_modifies BR.content.theSize, BnR.content.theSize, nBR.content.theSize, nBnR.content.theSize;
        for (VoeuClasse voe : voeuxClasses) {
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

        //@ assert BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == voeuxClasses.length;

        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        int nbBoursiersTotal = BR.size() + BnR.size();
        int nbResidentsTotal = BR.size() + nBR.size();

        //@ maintaining 0 <= nbAppeles && nbAppeles <= ordreAppel.length;
        //@ maintaining (\forall int i; 0 <= i && i < ordreAppel.length; ordreAppel[i] == null <==> nbAppeles <= i);
        //@ maintaining BR.content.theSize >= 0 && BnR.content.theSize >= 0 && nBR.content.theSize >= 0 && nBnR.content.theSize >= 0;
        //@ maintaining 0 <= BR.content.theSize + BnR.content.theSize && BR.content.theSize + BnR.content.theSize <= nbBoursiersTotal;
        //@ maintaining 0 <= BR.content.theSize + nBR.content.theSize && BR.content.theSize + nBR.content.theSize <= nbResidentsTotal;
        //@ maintaining nbAppeles + BR.content.theSize + BnR.content.theSize + nBR.content.theSize + nBnR.content.theSize == voeuxClasses.length;
        //@ loop_modifies nbAppeles;
        //@ loop_modifies BR.content.theSize, BnR.content.theSize, nBR.content.theSize, nBnR.content.theSize;
        //@ loop_modifies BR.values, BnR.values, nBR.values, nBnR.values;
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
