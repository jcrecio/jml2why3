package algo;

import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

import static algo.VoeuClasse.TypeCandidat;

/* BB The original algorithm with commented assertions and minimal requirements and
 * assumptions instead for assure the absence of arithmetic overflows and null-pointer
 * exceptions. */

public class GroupeClassement {

    public GroupeClassement() {}

    // public static void main(String[] args) {
    //     GroupeClassement groupeClassement = new GroupeClassement(0, 1, 1);
    //     groupeClassement.ajouterVoeu(new VoeuClasse(0, 1, true, false));
    //     groupeClassement.ajouterVoeu(new VoeuClasse(0, 2, false, true));
    //     groupeClassement.calculerOrdreAppel();
    // }

    // /*le code identifiant le groupe de classement dans la base de données
    //   Remarque: un même groupe de classement peut être commun à plusieurs formations
    // */
    // public final int C_GP_COD;

    // /* le taux minimum de boursiers dans ce groupe d'appel
    //    (nombre min de boursiers pour 100 candidats) */
    // public final int tauxMinBoursiersPourcents;

    // /* le taux minimum de candidats du secteur dans ce groupe d'appel
    //    (nombre min de candidats du secteur pour 100 candidats) */
    // public final int tauxMinDuSecteurPourcents;


    // //@ invariant 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    // //@ requires 0 <= tauxMinResidentsPourcents && tauxMinResidentsPourcents <= 100;
    // public GroupeClassement(int C_GP_COD, int tauxMinBoursiersPourcents, int tauxMinResidentsPourcents) {
    //     this.C_GP_COD = C_GP_COD;
    //     this.tauxMinBoursiersPourcents = tauxMinBoursiersPourcents;
    //     this.tauxMinDuSecteurPourcents = tauxMinResidentsPourcents;
    // }


    /* calcule de l'ordre d'appel */
    //@ requires 0 <= tauxMinBoursiersPourcents && tauxMinBoursiersPourcents <= 100;
    //@ requires 0 <= tauxMinDuSecteurPourcents && tauxMinDuSecteurPourcents <= 100;
    //@ requires voeuxClasses.length * 100 <= Integer.MAX_VALUE;
    //@ requires_redundantly voeuxClasses.length <= 21_474_836;
    //@ requires \nonnullelements(voeuxClasses);
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.length; 0 <= voeuxClasses[i].rang);
    //@ requires (\forall int i; 0 < i && i < voeuxClasses.length; voeuxClasses[i-1].rang <= voeuxClasses[i].rang);
    public VoeuClasse[] calculerOrdreAppel(VoeuClasse[] voeuxClasses, int tauxMinBoursiersPourcents, int tauxMinDuSecteurPourcents) {


        /* on crée autant de listes de candidats que de types de candidats,
           triées par ordre de classement */
        Map<TypeCandidat, Queue<VoeuClasse>> filesAttente
            = new HashMap<>();

        //@ loop_modifies filesAttente.content;
        //@ loop_invariant \invariant_for (filesAttente);
        for (TypeCandidat type : TypeCandidat.values()) {
            filesAttente.put(type, new LinkedList<>());
        }

        //@ // assume filesAttente.content.hasMap(TypeCandidat.BoursierDuSecteur);
        //@ // assume filesAttente.content.hasMap(TypeCandidat.BoursierHorsSecteur);
        //@ // assume filesAttente.content.hasMap(TypeCandidat.NonBoursierDuSecteur);
        //@ // assume filesAttente.content.hasMap(TypeCandidat.NonBoursierHorsSecteur);

        //@ // ghost Queue<VoeuClasse> boursierDuSecteur = filesAttente.get(TypeCandidat.BoursierDuSecteur);
        //@ // ghost Queue<VoeuClasse> boursierHorsSecteur = filesAttente.get(TypeCandidat.BoursierHorsSecteur);
        //@ // ghost Queue<VoeuClasse> nonBoursierDuSecteur = filesAttente.get(TypeCandidat.NonBoursierDuSecteur);
        //@ // ghost Queue<VoeuClasse> nonBoursierHorsSecteur = filesAttente.get(TypeCandidat.NonBoursierHorsSecteur);

        //@ // assert boursierDuSecteur != null && boursierHorsSecteur != null && nonBoursierDuSecteur != null && nonBoursierHorsSecteur != null;

        /* Chaque voeu classé est ventilé dans la liste correspondante,
           en fonction du type du candidat.
           Les quatre listes obtenues sont ordonnées par rang de classement,
           comme l'est la liste voeuxClasses. */
        int nbBoursiersTotal = 0;
        int nbResidentsTotal = 0;

        // voeuxClasses is sorted by precondition
        // /* on trie les candidats par classement,
        //    les candidats les mieux classés en tête de liste  */
        // voeuxClasses.sort((VoeuClasse v1, VoeuClasse v2) -> v1.rang - v2.rang);

        //@ // assume (\forall int i; 0 <= i && i < voeuxClasses.length; voeuxClasses[i].typeCandidat == TypeCandidat.BoursierDuSecteur || voeuxClasses[i].typeCandidat == TypeCandidat.BoursierHorsSecteur || voeuxClasses[i].typeCandidat == TypeCandidat.NonBoursierDuSecteur || voeuxClasses[i].typeCandidat == TypeCandidat.NonBoursierHorsSecteur);

        //@ loop_invariant \count <= voeuxClasses.length;
        //@ loop_invariant 0 <= nbBoursiersTotal && nbBoursiersTotal <= \count;
        //@ loop_invariant 0 <= nbResidentsTotal && nbResidentsTotal <= \count;
        //@ // loop_invariant \invariant_for(boursierDuSecteur);
        //@ // loop_invariant \invariant_for(boursierHorsSecteur);
        //@ // loop_invariant \invariant_for(nonBoursierDuSecteur);
        //@ // loop_invariant \invariant_for(nonBoursierHorsSecteur);
        //@ // loop_modifies boursierDuSecteur, boursierHorsSecteur, nonBoursierDuSecteur, nonBoursierHorsSecteur;
        //@ loop_modifies nbBoursiersTotal, nbResidentsTotal;
        for (VoeuClasse voe : voeuxClasses) {

            //@ // assume filesAttente.get(voe.typeCandidat) == boursierDuSecteur || filesAttente.get(voe.typeCandidat) == boursierHorsSecteur || filesAttente.get(voe.typeCandidat) == nonBoursierDuSecteur || filesAttente.get(voe.typeCandidat) == nonBoursierHorsSecteur;

            /* on ajoute le voeu à la fin de la file (FIFO) correspondante */
            filesAttente.get(voe.typeCandidat).add(voe);

            if (voe.estBoursier()) {
                nbBoursiersTotal++;
            }
            if (voe.estDuSecteur()) {
                nbResidentsTotal++;
            }
        }

        int nbBoursiersAppeles = 0;
        int nbResidentsAppeles = 0;

        /* la boucle ajoute les candidats un par un à la liste suivante,
           dans l'ordre d'appel */
        VoeuClasse[] ordreAppel = new VoeuClasse[voeuxClasses.length];

        //@ loop_invariant nbAppeles == \count;
        //@ loop_invariant 0 <= nbAppeles && nbAppeles <= voeuxClasses.length;
        //@ loop_invariant (\forall int i; 0 <= i && i < nbAppeles; ordreAppel[i] != null);
        //@ loop_invariant 0 <= nbBoursiersAppeles && nbBoursiersAppeles <= \count && nbBoursiersAppeles <= nbBoursiersTotal;
        //@ loop_invariant 0 <= nbResidentsAppeles && nbResidentsAppeles <= \count && nbResidentsAppeles <= nbResidentsTotal;
        //@ loop_modifies ordreAppel[*], nbBoursiersAppeles, nbResidentsAppeles;
        //@ decreasing voeuxClasses.length - nbAppeles;
        for (int nbAppeles=0; nbAppeles < voeuxClasses.length; nbAppeles++) {
            // while (ordreAppel.size() < voeuxClasses.size())

            /* on calcule lequel ou lesquels des critères boursiers et candidats du secteur
               contraignent le choix du prochain candidat dans l'ordre d'appel */
            boolean contrainteTauxBoursier
                = (nbBoursiersAppeles < nbBoursiersTotal)
                && (nbBoursiersAppeles * 100 < tauxMinBoursiersPourcents * (1 + nbAppeles));

            boolean contrainteTauxResident
                = (nbResidentsAppeles < nbResidentsTotal)
                && (nbResidentsAppeles * 100 < tauxMinDuSecteurPourcents * (1 + nbAppeles));

            /* on fait la liste des candidats satisfaisant
               les deux contraintes à la fois, ordonnée par rang de classement */
            Queue<VoeuClasse> eligibles = new PriorityQueue<>();

            //@ loop_invariant \invariant_for(eligibles);
            //@ loop_modifies eligibles.content;
            for (Queue<VoeuClasse> queue : filesAttente.values()) {
                if (!queue.isEmpty()) {
                    VoeuClasse voe = queue.peek();
                    if ((voe.estBoursier() || !contrainteTauxBoursier)
                        && (voe.estDuSecteur() || !contrainteTauxResident)) {
                        eligibles.add(voe);
                    }
                }
            }

            /* stocke le meilleur candidat à appeler tout en respectant
               les deux contraintes si possible
               ou à défaut seulement la contrainte sur le taux boursier */
            VoeuClasse meilleur = null;

            if (!eligibles.isEmpty()) {
                meilleur = eligibles.peek();
            } else {
                /* la liste peut être vide dans le cas où les deux contraintes
                   ne peuvent être satisfaites à la fois.
                   Dans ce cas nécessairement il y a une contrainte sur chacun des deux taux
                   (donc au moins un boursier non encore sélectionné)
                   et il ne reste plus de boursier du secteur,
                   donc il reste au moins un boursier hors-secteur */
                // assert contrainteTauxBoursier && contrainteTauxResident;
                // assert filesAttente.get(VoeuClasse.TypeCandidat.BoursierDuSecteur).isEmpty();
                // assert !filesAttente.get(VoeuClasse.TypeCandidat.BoursierHorsSecteur).isEmpty();

                //@ assume filesAttente.get(VoeuClasse.TypeCandidat.BoursierHorsSecteur) != null;

                Queue<VoeuClasse> CandidatsBoursierNonResident
                    = filesAttente.get(VoeuClasse.TypeCandidat.BoursierHorsSecteur);

                //@ assume 0 < CandidatsBoursierNonResident.content.theSize;

                meilleur = CandidatsBoursierNonResident.peek();
            }

            //@ assert meilleur != null;
            //@ assume filesAttente.get(meilleur.typeCandidat) != null;

            /* suppression du candidat choisi de sa file d'attente */
            Queue<VoeuClasse> queue = filesAttente.get(meilleur.typeCandidat);
            // assert meilleur == queue.peek();
            queue.poll();

            /* ajout du meilleur candidat à l'ordre d'appel*/
            ordreAppel[nbAppeles] = meilleur;

            /* mise à jour des compteurs */
            // nbAppeles++;

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
