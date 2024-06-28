class VoeuClasse {

    // public final int G_CN_COD;
    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;

    /*@ ensures this.rang == rang;
        ensures this.estBoursier == estBoursier;
        ensures this.estResident == estResident;
      @*/
    public /*@ pure @*/ VoeuClasse(
            int rang,
            boolean estBoursier,
            boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }
}

class Queue<E> {

    public final E[] values;
    public int first, end;

    /*@ public invariant first <= end;
        public invariant 0 <= end <= values.length;
        public invariant 0 <= first <= values.length;
        public invariant (\forall int i; first <= i && i < end; values[i] != null);
     @*/

    /*@ requires 0 <= capacity;
        ensures first == 0 && end == 0 && values.length == capacity;
        ensures_redundantly 0 == size();
      @*/
    public /*@ pure @*/ Queue(int capacity) {
        values = (E[]) new Object[capacity];
        first = 0;
        end = 0;
    }

    /*@ ensures \result == end - first;
        ensures 0 <= \result;
      @*/
    public /*@ pure @*/ int size() {
        return end - first;
    }

    //@ requires 0 <= i && i < size();
    //@ ensures \result == values[first+i];
    public /*@ pure @*/ E get(int i) {
        return values[first+i];
    }

    /*@ requires end < values.length;
        ensures values[\old(end)] == o;
        ensures (\forall int i; first <= i && i < \old(end); values[i] == \old(values)[i]);
        ensures end == \old(end) + 1;
        ensures \result;
        // // And to void a PossiblyBadArrayAssignment according to https://github.com/OpenJML/OpenJML/issues/628#issuecomment-407996574:
        // requires \type(E) <: \elemtype(\typeof(values));
      @*/
    public boolean add(E o) {
        values[end++] = o;
        return true;
    }

    /*@ public behavior
          requires 0 < size();
          ensures \result == values[first];
        also
        public behavior
          requires 0 == size();
          ensures \result == null;
      @*/
    public /*@ pure nullable @*/ E peek() {
        if (0 < size()) {
            return values[first];
        } else {
            //@ assert 0 == size();
            return null;
        }
    }

    /*@ public behavior
          requires 0 < size();
          ensures first == \old(first) + 1;
          ensures \result == values[\old(first)];
          writes first;
        also public behavior
          requires 0 == size();
          ensures \result == null;
      @*/
    public /*@ nullable @*/ E pop() {
        if (0 < size())
            return values[first++];
        else {
            //@ assert 0 == size();
            return null;
        }
    }
}

// class Test {

//     //@ requires a.length < Integer.MAX_VALUE;
//     //@ requires \nonnullelements(a);
//     int f1(VoeuClasse[] a) {
//         Queue q1 = new Queue(a.length);
//         /*@ loop_invariant 0 <= i && i <= a.length;
//             loop_invariant \nonnullelements(a);
//             loop_invariant \invariant_for(q1);
//             loop_invariant 0 <= q1.size() && q1.size() <= i;
//             loop_invariant (\forall int j; 0 <= j && j < q1.size();  q1.get(j).estBoursier);
//             loop_modifies i, q1.values[*], q1.end;
//           @*/
//         for (int i=0; i<a.length; i++) {
//             VoeuClasse v = a[i];
//             x: if (v.estBoursier) {
//                 /*@ assert (\forall int j; 0 <= j && j < q1.size();  q1.get(j).estBoursier);
//                   @*/
//                 q1.add(v);
//                 /*@ assert (\forall int j; 0 <= j && j < \old(q1, x).size();  \old(q1, x).get(j).estBoursier);
//                     assert (\forall int j; 0 <= j && j < q1.size()-1;  q1.get(j).estBoursier);
//                     assert q1.get(q1.size()-1).estBoursier;
//                   @*/
//             } else {
//                 /*@ assert (\forall int j; 0 <= j && j < \old(q1, x).size();  \old(q1, x).get(j).estBoursier);
//                     assert (\forall int j; 0 <= j && j < q1.size();  q1.get(j).estBoursier);
//                   @*/
//             }
//             /*@ assert (\forall int j; 0 <= j && j < \old(q1, x).size();  \old(q1, x).get(j).estBoursier);
//               @*/
//         }
//         return q1.size();
//     }

//     //@ requires a.length < Integer.MAX_VALUE;
//     //@ requires \nonnullelements(a);
//     //@ diverges false;
//     //@ assignable \nothing;
//     int f2(VoeuClasse[] a) {
//         Queue q1 = new Queue(a.length), q2 = new Queue(a.length);
//         /*@ loop_invariant 0 <= i && i <= a.length;
//           loop_invariant \invariant_for(q1) && \invariant_for(q2);
//           loop_invariant q1.size() + q2.size() == i;
//           loop_invariant 0 <= q1.size() && q1.size() <= i;
//           loop_invariant 0 <= q2.size() && q2.size() <= i;
//           loop_invariant (\forall int j; 0 <= j && j < q1.size();  q1.get(j).estBoursier);
//           loop_invariant (\forall int j; 0 <= j && j < q2.size(); !q2.get(j).estBoursier);
//           loop_modifies i, q1.values[*], q2.values[*], q1.end, q2.end;
//           @*/
//         for (int i=0; i<a.length; i++) {
//             if (a[i].estBoursier) {
//                 q1.add(a[i]);
//             } else {
//                 q2.add(a[i]);
//             }
//         }
//         return q1.size() + q2.size();
//     }
// }

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
    public GroupeClassement(
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
        requires (\forall int i; 0 <= i && i < voeuxClasses.length; voeuxClasses[i] != null);
        requires (\forall int i, j; 0 <= i < voeuxClasses.length && 0 <= j < voeuxClasses.length && i < j; voeuxClasses[i].rang < voeuxClasses[j].rang);
        // ensures \nonnullelements(\result);
      @*/
    public VoeuClasse[] calculerOrdreAppel(final VoeuClasse[] voeuxClasses) {

        /* on crée autant de listes de candidats ue de types de candidats,
            triées par ordre de classement */

        // Look, these are poor man's queues!
        Queue<VoeuClasse>
            BR = new Queue<>(voeuxClasses.length),
           BnR = new Queue<>(voeuxClasses.length),
           nBR = new Queue<>(voeuxClasses.length),
          nBnR = new Queue<>(voeuxClasses.length);

        //@ assume \invariant_for(BR) && \invariant_for(BnR) && \invariant_for(nBR) && \invariant_for(nBnR);

        /*@ loop_invariant 0 <= i && i <= voeuxClasses.length;
            loop_invariant \invariant_for(BR) && \invariant_for(BnR) && \invariant_for(nBR) && \invariant_for(nBnR);
            loop_invariant BR.size() + BnR.size() + nBR.size() + nBnR.size() == i;
            loop_invariant 0 <= BR.end && BR.end <= i;
            loop_invariant 0 <= BnR.end && BnR.end <= i;
            loop_invariant 0 <= nBR.end && nBR.end <= i;
            loop_invariant 0 <= nBnR.end && nBnR.end <= i;

            loop_invariant (\forall int j; BR.first <= j && j < BR.end;   BR.values[j].estBoursier && BR.values[j].estResident);
            loop_invariant (\forall int j; BnR.first <= j && j < BnR.end;  BnR.values[j].estBoursier && !BnR.values[j].estResident);
            loop_invariant (\forall int j; nBR.first <= j && j < nBR.end;  !nBR.values[j].estBoursier && nBR.values[j].estResident);
            loop_invariant (\forall int j; nBnR.first <= j && j < nBnR.end; !nBnR.values[j].estBoursier && !nBnR.values[j].estResident);

            loop_modifies i, BR.values[*], BnR.values[*], nBR.values[*], nBnR.values[*], BR.end, BnR.end, nBR.end, nBnR.end;
          @*/
        for (int i=0; i<voeuxClasses.length; i++) {
            final VoeuClasse voe = voeuxClasses[i];
            if (voe.estBoursier) {
                if (voe.estResident) {
                    BR.add(voe);
                } else {
                    BnR.add(voe);
                }
            } else {
                if (voe.estResident) {
                    nBR.add(voe);
                } else {
                    nBnR.add(voe);
                }
            }
        }

        int nbBoursiersTotal = BR.size() + BnR.size();
        int nbResidentsTotal = BR.size() + nBR.size();

        /* la boucle ajoute les candidats un par un à la liste suivante,
            dans l'ordre d'appel */
        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        /*@ loop_invariant 0 <= nbAppeles && nbAppeles <= ordreAppel.length;

            loop_invariant 0 <= BR.size() + BnR.size() && BR.size() + BnR.size() <= nbBoursiersTotal;
            loop_invariant 0 <= BR.size() + nBR.size() && BR.size() + nBR.size() <= nbBoursiersTotal;
            loop_invariant nbAppeles + BR.size() + BnR.size() + nBR.size() + nBnR.size() == voeuxClasses.length;

            loop_invariant (\forall int i; BR.first <= i   && i < BR.end;   BR.values[i].estBoursier && BR.values[i].estResident);
            loop_invariant (\forall int i; BnR.first <= i  && i < BnR.end;  BnR.values[i].estBoursier && !BnR.values[i].estResident);
            loop_invariant (\forall int i; nBR.first <= i  && i < nBR.end;  !nBR.values[i].estBoursier && nBR.values[i].estResident);
            loop_invariant (\forall int i; nBnR.first <= i && i < nBnR.end; !nBnR.values[i].estBoursier && !nBnR.values[i].estResident);

            loop_invariant (\forall int i; 0 <= i && i < nbAppeles; ordreAppel[i] != null);

            loop_modifies nbAppeles, BR.values[*], BnR.values[*], nBR.values[*], nBnR.values[*], BR.first, BnR.first, nBR.first, nBnR.first, ordreAppel[*];
          @*/
        for (int nbAppeles = 0; nbAppeles < voeuxClasses.length; nbAppeles++) {

            final int nbBoursierRestants = BR.size() + BnR.size();
            final int nbResidentsRestants = BR.size() + nBR.size();
            final int nbBoursiersAppeles = nbBoursiersTotal - nbBoursierRestants;
            final int nbResidentsAppeles = nbResidentsTotal - nbResidentsRestants;

            /* on calcule lequel ou lesquels des critères boursiers et candidats du secteur
                contraignent le choix du prochain candidat dans l'ordre d'appel */
            boolean contrainteTauxBoursier
                    = (nbBoursiersAppeles < nbBoursiersTotal)
                    && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxBoursier ==> 0 < BR.size() || 0 < BnR.size();

            boolean contrainteTauxResident
                    = (nbResidentsAppeles < nbResidentsTotal)
                    && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            //@ assert contrainteTauxResident ==> 0 < BR.size() || 0 < nBR.size();

            // assert 0 < BR.size() || 0 < BnR.size() || 0 < nBR.size() || 0 < nBnR.size();

            /*@ nullable @*/ VoeuClasse meilleur = null;
            if (0 < BR.size()) {
                meilleur = BR.peek();
            }
            if (0 < nBR.size() && !contrainteTauxBoursier && (meilleur == null || meilleur.rang < nBR.peek().rang)) {
                meilleur = nBR.peek();
            }
            if (0 < BnR.size() && !contrainteTauxResident && (meilleur == null || meilleur.rang < BnR.peek().rang)) {
                meilleur = BnR.peek();
            }
            if (0 < nBnR.size() && !contrainteTauxBoursier && !contrainteTauxResident && (meilleur == null || meilleur.rang < nBnR.peek().rang)) {
                meilleur = nBnR.peek();
            }
            if (meilleur == null) {
                // assert contrainteTauxBoursier && contrainteTauxResident;
                // assert 0 == BR.size();
                //@ assert 0 < BnR.size();
                meilleur = BnR.peek();
            }

            //@ assert meilleur == BR.peek() || meilleur == BnR.peek() || meilleur == nBR.peek() || meilleur == nBnR.peek();

            /* suppression du candidat choisi de sa file d'attente */
             if (meilleur.estBoursier) {
                if (meilleur.estResident) {
                    //@ assert 0 < BR.size();
                    BR.pop();
                } else {
                    //@ assert 0 < BnR.size();
                    BnR.pop();
                }
            } else {
                if (meilleur.estResident) {
                    //@ assert 0 < nBR.size();
                    nBR.pop();
                } else {
                    //@ assert 0 < nBnR.size();
                    nBnR.pop();
                }
            }

            /* ajout du meilleur candidat à l'ordre d'appel*/
            ordreAppel[nbAppeles] = meilleur;
        }

        /* retourne les candidats classés dans l'ordre d'appel */
        return ordreAppel;
    }
}

public class GroupeClassement__array_queue {}
