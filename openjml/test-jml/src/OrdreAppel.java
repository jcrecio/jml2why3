import java.util.PriorityQueue;
import java.util.Queue;

public class OrdreAppel {

    /* calcule de l'ordre d'appel */
    //@ requires voeuxClasses.length * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rangAppel
    //@ requires_redundantly voeuxClasses.length < 21_474_836;
    //@ requires \nonnullelements(voeuxClasses);
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.length; 0 <= voeuxClasses[i].rang);
    //@ requires (\forall int i; 0 < i && i < voeuxClasses.length; voeuxClasses[i-1].rang <= voeuxClasses[i].rang);
    //@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    //@ requires 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100;
    public VoeuClasse[] calculerOrdreAppel(VoeuClasse[] voeuxClasses, int tauxMinBoursiersPourcents, int tauxMinDuSecteurPourcents) {
        /* on crée autant de listes de candidats que de types de candidats, 
            triées par ordre de classement */
        FilesAttente filesAttente = new FilesAttente();
//    	Map<TypeCandidat, Queue<VoeuClasse>> filesAttente = new HashMap<>();
//      for (TypeCandidat type : TypeCandidat.values()) {
//          filesAttente.put(type, new LinkedList<>());
//      }

        // /* on trie les candidats par classement,
        //    les candidats les mieux classés en tête de liste  */
        // Arrays.sort(voeuxClasses, (VoeuClasse v1, VoeuClasse v2) -> v2.rang - v1.rang);
        // Make it instead a precondition that voeuxClasses is sorted, because
        // 1) using Arrays.sort triggers the OpenJML warning:
        //    NOT IMPLEMENTED: Not yet supported feature in converting BasicPrograms to SMTLIB: JML Quantified expression using \num_of
        // 2) and the following assert triggers the warning:
        //    there is no feasible path to program point before explicit assert statement
        // //@ assert (\forall int i; i < 0 && i < voeuxClasses.length; voeuxClasses[i-1].rang <= voeuxClasses[i].rang);

        /* Chaque voeu classé est ventilé dans la liste correspondante, 
        en fonction du type du candidat. 
        Les quatre listes obtenues sont ordonnées par rang de classement, 
        comme l'est la liste voeuxClasses. */
        int nbBoursiersTotal = 0;
        int nbResidentsTotal = 0;

        //@ maintaining \count <= voeuxClasses.length;
        //@ maintaining 0 <= nbBoursiersTotal && nbBoursiersTotal <= \count;
        //@ maintaining 0 <= nbResidentsTotal && nbResidentsTotal <= \count;
        for (VoeuClasse voe : voeuxClasses) {

            /* on ajoute le voeu à la fin de la file (FIFO) correspondante */
            filesAttente.add(voe);

            if (voe.estBoursier()) {
                nbBoursiersTotal++;
            }
            if (voe.estDuSecteur()) {
                nbResidentsTotal++;
            }
        }

        int nbAppeles = 0;
        int nbBoursiersAppeles = 0;
        int nbResidentsAppeles = 0;

        /* la boucle ajoute les candidats un par un à la liste suivante,
            dans l'ordre d'appel */
        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        //@ maintaining nbAppeles == \count;
        //@ maintaining 0 <= nbAppeles && nbAppeles <= voeuxClasses.length;
        //@ maintaining (\forall int i; 0 <= i && i < nbAppeles; ordreAppel[i] != null);
        //@ maintaining 0 <= nbBoursiersAppeles && nbBoursiersAppeles <= \count && nbBoursiersAppeles <= nbBoursiersTotal;
        //@ maintaining 0 <= nbResidentsAppeles && nbResidentsAppeles <= \count && nbResidentsAppeles <= nbResidentsTotal;
        //@ decreasing voeuxClasses.length - nbAppeles;
        while (nbAppeles < voeuxClasses.length) {
        //     /* on calcule lequel ou lesquels des critères boursiers et candidats du secteur
        //         contraignent le choix du prochain candidat dans l'ordre d'appel */
            boolean contrainteTauxBoursier
                    = (nbBoursiersAppeles < nbBoursiersTotal)
                    && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            boolean contrainteTauxResident
                    = (nbResidentsAppeles < nbResidentsTotal)
                    && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            /* on fait la liste des candidats satisfaisant
                les deux contraintes à la fois, ordonnée par rang de classement */
            Queue<VoeuClasse> eligibles = new PriorityQueue<>();

            for (Queue<VoeuClasse> queue : filesAttente.values()) {
                if (!queue.isEmpty()) {
                    VoeuClasse voe = queue.peek();
                    if ((voe.estBoursier() || !contrainteTauxBoursier) && (voe.estDuSecteur() || !contrainteTauxResident)) {
                        eligibles.add(voe);
                    }
                }
            }
            /* stocke le meilleur candidat à appeler tout en respectant
            les deux contraintes si possible 
            ou à défaut seulement la contrainte sur le taux boursier */
            final VoeuClasse meilleur;

            if (!eligibles.isEmpty()) {
                meilleur = eligibles.peek();
            } else {
                /* la liste peut être vide dans le cas où les deux contraintes 
                ne peuvent être satisfaites à la fois. 
                Dans ce cas nécessairement il y a une contrainte sur chacun des deux taux 
                (donc au moins un boursier non encore sélectionné) 
                et il ne reste plus de boursier du secteur, 
                donc il reste au moins un boursier hors-secteur */
                assert contrainteTauxBoursier && contrainteTauxResident;
                assert filesAttente.get(VoeuClasse.TypeCandidat.BoursierDuSecteur).isEmpty();
                assert !filesAttente.get(VoeuClasse.TypeCandidat.BoursierHorsSecteur).isEmpty();

                Queue<VoeuClasse> CandidatsBoursierNonResident
                        = filesAttente.get(TypeCandidat.BoursierHorsSecteur);

                meilleur = CandidatsBoursierNonResident.peek();
            }

            /* suppression du candidat choisi de sa file d'attente */
            Queue<VoeuClasse> queue = filesAttente.get(meilleur.typeCandidat);
            assert meilleur == queue.peek();
            queue.poll();

            /* ajout du meilleur candidat à l'ordre d'appel*/
            ordreAppel[nbAppeles] = meilleur;

            /* mise à jour des compteurs */
            nbAppeles++;

            if (meilleur.estBoursier()) {
                nbBoursiersAppeles++;
            }
            if (meilleur.estDuSecteur()) {
                nbResidentsAppeles++;
            }
        }

        /* mise à jour des ordres d'appel */
        int rangAppel = 1;
         //@ maintaining rangAppel == \count + 1;
         //@ maintaining \count <= voeuxClasses.length;
        for (VoeuClasse v : ordreAppel) {
            v.rangAppel = rangAppel;
            rangAppel++;
        }

        /* retourne les candidats classés dans l'ordre d'appel */
        return ordreAppel;
    }
}
