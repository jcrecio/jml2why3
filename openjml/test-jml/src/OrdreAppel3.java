import java.util.LinkedList;
import java.util.Queue;

public class OrdreAppel3 {

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

        //@ maintaining BR.size() + BnR.size() + nBR.size() + nBnR.size() == \count;
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
        
        int nbBoursiersTotal = BR.size() + BnR.size();
        int nbResidentsTotal = nBR.size() + nBnR.size();

        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        //@ maintaining 0 <= nbAppeles && nbAppeles <= voeuxClasses.length;
        //@ maintaining BR.size() + BnR.size() + nBR.size() + nBnR.size() == voeuxClasses.length - nbAppeles;
        for (int nbAppeles = 0; nbAppeles < voeuxClasses.length; nbAppeles++) {
        	
        	//@ assert !BR.isEmpty() || !BnR.isEmpty() || !nBR.isEmpty() || !nBnR.isEmpty();

            int nbBoursierRestants = BR.size() - BnR.size();
            int nbResidentsRestants = BR.size() - nBR.size();
            int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            boolean contrainteTauxBoursier = 0 < nbBoursierRestants
                && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            //@ assert (contrainteTauxBoursier ==> (!BR.isEmpty() || !BnR.isEmpty()));

            boolean contrainteTauxResident = 0 < nbResidentsRestants
                && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            //@ assert (contrainteTauxResident ==> (!BR.isEmpty() || !nBR.isEmpty()));
            
            /*@ nullable @*/ Queue<VoeuClasse> meilleurQueue = null;
            if (!BR.isEmpty())
            	meilleurQueue = BR;
            if (!BnR.isEmpty() && !contrainteTauxResident && (meilleurQueue == null || meilleurQueue.peek().rang > BnR.peek().rang))
            	meilleurQueue = BnR;
            if (!nBR.isEmpty() && !contrainteTauxBoursier && (meilleurQueue == null || meilleurQueue.peek().rang > nBR.peek().rang))
            	meilleurQueue = nBR;
            if (!nBnR.isEmpty() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleurQueue == null || meilleurQueue.peek().rang > nBnR.peek().rang))
            	meilleurQueue = nBnR;
            
            //@ assert meilleurQueue != null && !meilleurQueue.isEmpty();
            ordreAppel[nbAppeles] = meilleurQueue.poll();
        }
        return ordreAppel;
    }
}
