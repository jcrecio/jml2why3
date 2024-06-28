import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

class FilesAttente {
    private /*@ spec_public @*/ final Queue<VoeuClasse>
        boursierDuSecteur = new LinkedList<>(),
        boursierHorsSecteur = new LinkedList<>(),
    	nonBoursierDuSecteur = new LinkedList<>(),
    	nonBoursierHorsSecteur = new LinkedList<>();
    
//    //@ model Set<VoeuClasse> boursier;
//    //@ represents boursier <- getBoursiers();
//    //@ model Set<VoeuClasse> residents;
//    //@ represents residents <- getResidents();
//    
//    //@ ensures (\forall VoeuClasse v; \result.contains(v) <==> boursierDuSecteur.contains(v) || boursierHorsSecteur.contains(v));
//    //@ pure helper
//    Set<VoeuClasse> getBoursiers() {
//    	Set<VoeuClasse> res = new HashSet<>();
//    	res.addAll(boursierDuSecteur);
//    	res.addAll(boursierHorsSecteur);
//    	return res;
//    }
//    //@ ensures (\forall VoeuClasse v; \result.contains(v) <==> boursierDuSecteur.contains(v) || nonBoursierDuSecteur.contains(v));
//    //@ pure helper
//    Set<VoeuClasse> getResidents() {
//    	Set<VoeuClasse> res = new HashSet<>();
//    	res.addAll(boursierDuSecteur);
//    	res.addAll(nonBoursierDuSecteur);
//    	return res;
//    }

    //@ ensures \result.size() == 4;
    // @ ensures (\forall Queue<VoeuClasse> q; \result.contains(q) <==> q == boursierDuSecteur || q == boursierHorsSecteur || q == nonBoursierDuSecteur || q == nonBoursierHorsSecteur);
    //@ ensures \result.contains(boursierDuSecteur);
    //@ ensures \result.contains(boursierHorsSecteur);
    //@ ensures \result.contains(nonBoursierDuSecteur);
    //@ ensures \result.contains(nonBoursierHorsSecteur);
    //@ ensures (\forall Queue<VoeuClasse> q; \result.contains(q); q == boursierDuSecteur || q == boursierHorsSecteur || q == nonBoursierDuSecteur || q == nonBoursierHorsSecteur);
    //@ pure
    Collection<Queue<VoeuClasse>> values() {
    	List<Queue<VoeuClasse>> res = new LinkedList<>();
    	res.add(boursierDuSecteur);
    	res.add(boursierHorsSecteur);
    	res.add(nonBoursierDuSecteur);
    	res.add(nonBoursierHorsSecteur);
    	return res;
    }
    
    void add(VoeuClasse voe) {
    	select(voe.typeCandidat).add(voe);
    }

    //@ requires t.estBoursier() && t.estDuSecteur();
    //@ ensures \result == boursierDuSecteur;
    //@ also
    //@ requires t.estBoursier() && !t.estDuSecteur();
    //@ ensures \result == boursierHorsSecteur;
    //@ also
    //@ requires !t.estBoursier() && t.estDuSecteur();
    //@ ensures \result == nonBoursierDuSecteur;
    //@ also
    //@ requires !t.estBoursier() && !t.estDuSecteur();
    //@ ensures \result == nonBoursierHorsSecteur;
    //@ pure
    private Queue<VoeuClasse> select(TypeCandidat t) {
        if (t.estBoursier()) {
            if (t.estDuSecteur())
                return boursierDuSecteur;
            else
                return boursierHorsSecteur;
        } else {
            if (t.estDuSecteur())
                return nonBoursierDuSecteur;
            else
                return nonBoursierHorsSecteur;
        }
    }
    
    public Queue<VoeuClasse> get(TypeCandidat t) {
    	return new LinkedList<>(select(t));
    }
}
