/* Verification takes a while to verify, don't give up!

   $ java -jar openjml-v0.3.jar -esc -progress GroupeClassement__everything_arrays.java
   Proving methods in VoeuClasse
   Starting proof of VoeuClasse.VoeuClasse(int,boolean,boolean) with prover z3_4_3
   VoeuClasse.VoeuClasse Method assertions are validated [0.06 secs]
   GroupeClassement__everything_arrays.java:15: Feasibility check #1 - end of preconditions : OK [0.00 secs]
   GroupeClassement__everything_arrays.java:15: Feasibility check #2 - at program exit : OK [0.00 secs]
   Completed proof of VoeuClasse.VoeuClasse(int,boolean,boolean) with prover z3_4_3 - no warnings [0.17 secs]
   Completed proving methods in VoeuClasse [0.21 secs]
   Proving methods in GroupeClassement
   Starting proof of GroupeClassement.GroupeClassement(int,int,int) with prover z3_4_3
   GroupeClassement.GroupeClassement Method assertions are validated [0.04 secs]
   GroupeClassement__everything_arrays.java:46: Feasibility check #1 - end of preconditions : OK [0.00 secs]
   GroupeClassement__everything_arrays.java:46: Feasibility check #2 - at program exit : OK [0.00 secs]
   Completed proof of GroupeClassement.GroupeClassement(int,int,int) with prover z3_4_3 - no warnings [0.09 secs]
   Starting proof of GroupeClassement.calculerOrdreAppel(VoeuClasse[]) with prover z3_4_3
    GroupeClassement.calculerOrdreAppel Method assertions are validated [178.12 secs]
   GroupeClassement__everything_arrays.java:64: Feasibility check #1 - end of preconditions : OK [321.56 secs]
   GroupeClassement__everything_arrays.java:160: Feasibility check #2 - before explicit assert statement : OK [101.85 secs]
   GroupeClassement__everything_arrays.java:166: Feasibility check #3 - before explicit assert statement : OK [1170.22 secs]
   GroupeClassement__everything_arrays.java:182: Feasibility check #4 - before explicit assert statement : OK [243.96 secs]
   GroupeClassement__everything_arrays.java:185: Feasibility check #5 - before explicit assert statement : OK [41.14 secs]
   GroupeClassement__everything_arrays.java:187: Feasibility check #6 - before explicit assert statement : OK [45.19 secs]
   GroupeClassement__everything_arrays.java:195: Feasibility check #7 - before explicit assert statement : OK [75.17 secs]
   GroupeClassement__everything_arrays.java:198: Feasibility check #8 - before explicit assert statement : OK [2855.19 secs]
   GroupeClassement__everything_arrays.java:203: Feasibility check #9 - before explicit assert statement : OK [92.09 secs]
   GroupeClassement__everything_arrays.java:206: Feasibility check #10 - before explicit assert statement : OK [28.33 secs]
   GroupeClassement__everything_arrays.java:64: Feasibility check #11 - at program exit : OK [37.37 secs]
   Completed proof of GroupeClassement.calculerOrdreAppel(VoeuClasse[]) with prover z3_4_3 - no warnings [5190.28 secs]
   Completed proving methods in GroupeClassement [5190.46 secs]
   Proving methods in GroupeClassement__everything_arrays
   Starting proof of GroupeClassement__everything_arrays.GroupeClassement__everything_arrays() with prover z3_4_3
   GroupeClassement__everything_arrays.GroupeClassement__everything_arrays Method assertions are validated [0.02 secs]
   GroupeClassement__everything_arrays.java:220: Feasibility check #1 - end of preconditions : OK [0.00 secs]
   GroupeClassement__everything_arrays.java:220: Feasibility check #2 - at program exit : OK [0.00 secs]
   Completed proof of GroupeClassement__everything_arrays.GroupeClassement__everything_arrays() with prover z3_4_3 - no warnings [0.03 secs]
   Completed proving methods in GroupeClassement__everything_arrays [0.08 secs]
   Note: Summary:
       Valid:        4
       Invalid:      0
       Infeasible:   0
       Timeout:      0
       Error:        0
       Skipped:      0
      TOTAL METHODS: 4
      Classes:       3 proved of 3
      Model Classes: 0
      Model methods: 0 proved of 0
      DURATION:       5191.3 secs */

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

class VoeuClasse {

    // public final int G_CN_COD;
    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;

    public /*@ pure @*/ VoeuClasse(
            int rang,
            boolean estBoursier,
            boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }
}

class GroupeClassement {

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
            int C_GP_COD,
            int tauxMinBoursiersPourcents,
            int tauxMinResidentsPourcents) {
        this.C_GP_COD = C_GP_COD;
        this.tauxMinBoursiersPourcents = tauxMinBoursiersPourcents;
        this.tauxMinDuSecteurPourcents = tauxMinResidentsPourcents;
    }

    /* calcule de l'ordre d'appel */
    /*@ requires voeuxClasses.length * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rangAppel
        requires_redundantly voeuxClasses.length < 21_474_836;
        requires \nonnullelements(voeuxClasses);
        requires (\forall int i, j; 0 <= i < voeuxClasses.length && 0 <= j < voeuxClasses.length && i < j; voeuxClasses[i].rang < voeuxClasses[j].rang);
        ensures \nonnullelements(\result);
        assignable \nothing;
      @*/
    public VoeuClasse[] calculerOrdreAppel(final VoeuClasse[] voeuxClasses) {

        /* on crée autant de listes de candidats ue de types de candidats,
            triées par ordre de classement */

        // Look at these poor man's queues!
        VoeuClasse[]
            BR = new VoeuClasse[voeuxClasses.length],
            BnR = new VoeuClasse[voeuxClasses.length],
            nBR = new VoeuClasse[voeuxClasses.length],
            nBnR = new VoeuClasse[voeuxClasses.length];
        int BR_end = 0, BnR_end = 0, nBR_end = 0, nBnR_end = 0;

        /*@ loop_invariant 0 <= i && i <= voeuxClasses.length;
            loop_invariant BR_end + BnR_end + nBR_end + nBnR_end == i;
            loop_invariant 0 <= BR_end && BR_end <= i;
            loop_invariant 0 <= BnR_end && BnR_end <= i;
            loop_invariant 0 <= nBR_end && nBR_end <= i;
            loop_invariant 0 <= nBnR_end && nBnR_end <= i;

            loop_invariant (\forall int j; 0 <= j && j < BR_end;   BR[j] != null);
            loop_invariant (\forall int j; 0 <= j && j < BnR_end;  BnR[j] != null);
            loop_invariant (\forall int j; 0 <= j && j < nBR_end;  nBR[j] != null);
            loop_invariant (\forall int j; 0 <= j && j < nBnR_end; nBnR[j] != null);

            loop_invariant (\forall int j; 0 <= j && j < BR_end;    BR[j].estBoursier   &&  BR[j].estResident);
            loop_invariant (\forall int j; 0 <= j && j < BnR_end;   BnR[j].estBoursier  && !BnR[j].estResident);
            loop_invariant (\forall int j; 0 <= j && j < nBR_end;  !nBR[j].estBoursier  &&  nBR[j].estResident);
            loop_invariant (\forall int j; 0 <= j && j < nBnR_end; !nBnR[j].estBoursier && !nBnR[j].estResident);

            loop_modifies i, BR[*], BnR[*], nBR[*], nBnR[*];
            loop_modifies BR_end, BnR_end, nBR_end, nBnR_end;
          @*/
        for (int i=0; i<voeuxClasses.length; i++) {
            final VoeuClasse voe = voeuxClasses[i];
            if (voe.estBoursier) {
                if (voe.estResident) {
                    BR[BR_end++] = voe;
                } else {
                    BnR[BnR_end++] = voe;
                }
            } else {
                if (voe.estResident) {
                    nBR[nBR_end++] = voe;
                } else {
                    nBnR[nBnR_end++] = voe;
                }
            }
        }

        int nbBoursiersTotal = BR_end + BnR_end;
        int nbResidentsTotal = BR_end + nBR_end;

        int BR_first = 0, BnR_first = 0, nBR_first = 0, nBnR_first = 0;

        /* la boucle ajoute les candidats un par un à la liste suivante,
            dans l'ordre d'appel */
        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        /*@ loop_invariant 0 <= nbAppeles && nbAppeles <= ordreAppel.length;
            loop_invariant 0 <= BR_first && BR_first <= BR_end;
            loop_invariant 0 <= BnR_first && BnR_first <= BnR_end;
            loop_invariant 0 <= nBR_first && nBR_first <= nBR_end;
            loop_invariant 0 <= nBnR_first && nBnR_first <= nBnR_end;
            loop_invariant 0 <= (BR_end-BR_first) + (BnR_end-BnR_first) && (BR_end-BR_first) + (BnR_end-BnR_first) <= nbBoursiersTotal;
            loop_invariant 0 <= (BR_end-BR_first) + (nBR_end-nBR_first) && (BR_end-BR_first) + (nBR_end-nBR_first) <= nbResidentsTotal;
            loop_invariant nbAppeles + (BR_end-BR_first) + (BnR_end-BnR_first) + (nBR_end-nBR_first) + (nBnR_end-nBnR_first) == voeuxClasses.length;

            loop_invariant (\forall int j; BR_first <= j &&   j < BR_end;     BR[j] != null);
            loop_invariant (\forall int j; BnR_first <= j &&  j < BnR_end;   BnR[j] != null);
            loop_invariant (\forall int j; nBR_first <= j &&  j < nBR_end;   nBR[j] != null);
            loop_invariant (\forall int j; nBnR_first <= j && j < nBnR_end; nBnR[j] != null);

            loop_invariant (\forall int i; BR_first <= i   && i < BR_end;   BR[i].estBoursier && BR[i].estResident);
            loop_invariant (\forall int i; BnR_first <= i  && i < BnR_end;  BnR[i].estBoursier && !BnR[i].estResident);
            loop_invariant (\forall int i; nBR_first <= i  && i < nBR_end;  !nBR[i].estBoursier && nBR[i].estResident);
            loop_invariant (\forall int i; nBnR_first <= i && i < nBnR_end; !nBnR[i].estBoursier && !nBnR[i].estResident);

            loop_invariant (\forall int i; 0 <= i && i < nbAppeles; ordreAppel[i] != null);

            loop_modifies nbAppeles, ordreAppel[*];
            loop_modifies BR_first, BnR_first, nBR_first, nBnR_first;
          @*/
        for (int nbAppeles = 0; nbAppeles < voeuxClasses.length; nbAppeles++) {

            final int nbBoursierRestants = (BR_end-BR_first) + (BnR_end-BnR_first);
            final int nbResidentsRestants = (BR_end-BR_first) + (nBR_end-nBR_first);
            final int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            final int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            /* on calcule lequel ou lesquels des critères boursiers et candidats du secteur
                contraignent le choix du prochain candidat dans l'ordre d'appel */
            boolean contrainteTauxBoursier
                    = (nbBoursiersAppeles < nbBoursiersTotal)
                    && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxBoursier ==> 0 < BR_end-BR_first || 0 < BnR_end-BnR_first;

            boolean contrainteTauxResident
                    = (nbResidentsAppeles < nbResidentsTotal)
                    && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxResident ==> 0 < BR_end-BR_first || 0 < nBR_end-nBR_first;

            /*@ nullable @*/ VoeuClasse meilleur = null;
            if (0 < BR_end-BR_first) {
                meilleur = BR[BR_first];
            }
            if (0 < nBR_end-nBR_first && !contrainteTauxBoursier && (meilleur == null || meilleur.rang < nBR[nBR_first].rang)) {
                meilleur = nBR[nBR_first];
            }
            if (0 < BnR_end-BnR_first && !contrainteTauxResident && (meilleur == null || meilleur.rang < BnR[BnR_first].rang)) {
                meilleur = BnR[BnR_first];
            }
            if (0 < nBnR_end-nBnR_first && !contrainteTauxBoursier && !contrainteTauxResident && (meilleur == null || meilleur.rang < nBnR[nBnR_first].rang)) {
                meilleur = nBnR[nBnR_first];
            }
            if (meilleur == null) {
                //@ assert 0 < BnR_end-BnR_first;
                meilleur = BnR[BnR_first];
            }
            /*@ assert meilleur != null; @*/

            /*@ assert (0 < BR_end-BR_first     && meilleur == BR[BR_first]) ||
                       (0 < BnR_end-BnR_first   && meilleur == BnR[BnR_first]) ||
                       (0 < nBR_end-nBR_first   && meilleur == nBR[nBR_first]) ||
                       (0 < nBnR_end-nBnR_first && meilleur == nBnR[nBnR_first]); @*/

            /* suppression du candidat choisi de sa file d'attente */
             if (meilleur.estBoursier) {
                if (meilleur.estResident) {
                    //@ assert 0 < BR_end-BR_first;
                    BR_first++;
                } else {
                    //@ assert 0 < BnR_end-BnR_first;
                    BnR_first++;
                }
            } else {
                if (meilleur.estResident) {
                    //@ assert 0 < nBR_end-nBR_first;
                    nBR_first++;
                } else {
                    //@ assert 0 < nBnR_end-nBnR_first;
                    nBnR_first++;
                }
            }

            /* ajout du meilleur candidat à l'ordre d'appel*/
            ordreAppel[nbAppeles] = meilleur;
        }

        /* retourne les candidats classés dans l'ordre d'appel */
        return ordreAppel;
    }
}

public class GroupeClassement__everything_arrays {}
