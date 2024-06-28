import java.util.Arrays;
import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

class VoeuClasse {

    public final boolean boursier;
    public final boolean resident;
    public final int rang; // Index in list of wishes
    // public int rangAppel; // Value in Permutation.inv

    /*@ public invariant 1 <= rang; @*/

    /*@ requires 1 <= rang; @*/
    /*@ pure @*/ public VoeuClasse(
            final int rang,
            final boolean boursier,
            final boolean resident) {
        this.rang = rang;
        this.boursier = boursier;
        this.resident = resident;
    }
}

class Permutation {
    public final int[] map;
    public final int[] inv; // TODO ghostify

    /*@ // public invariant map != inv;
        public invariant map.length == inv.length;
        public invariant (\forall int i; 0 <= i && i < map.length;
          0 <= map[i] && map[i] < map.length && inv[map[i]] == i);
        public invariant (\forall int i; 0 <= i && i < map.length;
          0 <= inv[i] && inv[i] < map.length && map[inv[i]] == i); @*/

    // // Errors with
    // // [@vc:sp]
    // // ((Utils.ignore (this.map <- map0));
    // // (Utils.ignore (this.inv <- inv0)))
    // // This expression prohibits further usage of the variable map0 or any function that depends on it
    // /*@ requires map0.length == inv0.length;
    //     requires (\forall int j; 0 <= j && j < map0.length; 0 <= map0[j] && map0[j] < map0.length);
    //     requires (\forall int j; 0 <= j && j < map0.length; inv0[map0[j]] == j);
    //     requires (\forall int j; 0 <= j && j < map0.length; 0 <= inv0[j] && inv0[j] < map0.length);
    //     requires (\forall int j; 0 <= j && j < map0.length; map0[inv0[j]] == j);
    //     ensures map.length == map0.length;
    //     ensures (\forall int j; 0 <= j && j < map.length; map[j] == map0[j]);
    //     ensures (\forall int j; 0 <= j && j < map.length; inv[j] == inv0[j]); @*/
    // Permutation(final int[] map0, final int[] inv0) {
    //     this.map = map0;
    //     this.inv = inv0;
    // }


    /*@ requires map0.length == inv0.length;
        requires (\forall int j; 0 <= j && j < map0.length;
          0 <= map0[j] && map0[j] < map0.length && inv0[map0[j]] == j);
        requires (\forall int j; 0 <= j && j < map0.length;
          0 <= inv0[j] && inv0[j] < map0.length && map0[inv0[j]] == j);
        ensures this.map.length == map0.length;
        ensures this.map.length == inv.length;
        ensures (\forall int j; 0 <= j && j < map.length; this.map[j] == map0[j]);
        ensures (\forall int j; 0 <= j && j < map.length; this.inv[j] == inv0[j]); @*/
    Permutation(final int[] map0, final int[] inv0) {
        this.map = map0.clone();
        this.inv = inv0.clone();
    }
}

class GroupeClassement {

    /*le code identifiant le groupe de classement dans la base de données
        Remarque: un même groupe de classement peut être commun à plusieurs formations
     */
    public final int C_GP_COD;

    /* le taux minimum de boursiers dans ce groupe d'appel
        (nombre min de boursiers pour 100 candidats) */
    public final int tauxBoursiers;

    /* le taux minimum de candidats du secteur dans ce groupe d'appel
        (nombre min de candidats du secteur pour 100 candidats) */
    public final int tauxResidents;

    /*@ invariant 0 <= tauxBoursiers && tauxBoursiers <= 100;
        invariant 0 <= tauxResidents && tauxResidents <= 100; @*/

    /*@ requires 0 <= tauxBoursiers && tauxBoursiers <= 100;
        requires 0 <= tauxMinResidentsPourcents && tauxMinResidentsPourcents <= 100; @*/
    public /*@ pure @*/ GroupeClassement(
            final int C_GP_COD,
            final int tauxBoursiers,
            final int tauxMinResidentsPourcents) {
        this.C_GP_COD = C_GP_COD;
        this.tauxBoursiers = tauxBoursiers;
        this.tauxResidents = tauxMinResidentsPourcents;
    }

    /*@ ensures \result == (\forall int i; 0 <= i && i < q.size(); 0 <= q._get(i) && q._get(i) < vs.size());
        public static pure model boolean inRange(final LinkedList<VoeuClasse> vs, final Queue<Integer> q);

        ensures \result == (\forall int i; 0 <= i && i < q.size();   vs.get(q._get(i)).boursier == boursier && vs.get(q._get(i)).resident == resident);
        public static pure model boolean homogenic(final LinkedList<VoeuClasse> vs, final Queue<Integer> q, final boolean boursier, final boolean resident);

        ensures \result == (\num_of int j; l <= j && j < u; a[j] == x);
        public static pure model int occArray(final int x, final int[] a, final int l, final int u);

        ensures \result == (\num_of int j; 0 <= j && j < Q.size(); Q._get(j) == x);
        public static pure model int occQueue(final int x, final Queue<Integer> Q); @*/

    /*@ // Propriété 4.1 b: Un candidat résident boursier qui a le rang r dans le classement
        // pédagogique aura donc un rang inférieur ou égal à r dans l'ordre d'appel.
        requires 0 <= n && n <= vs.size();
        requires vs.size() == inv.length;
        ensures \result == (\forall int j; 0 <= j && j < n; vs.get(j).boursier && vs.get(j).resident ==>
            // j ≘ index in voeuxClasses ≘ rang; inv[j] ≘ rangAppel
          inv[j] <= j);
        public static pure model boolean property41b(final LinkedList<VoeuClasse> vs, final int[] inv, final int n); @*/

    /*@ requires 0 <= n && n <= vs.size();
        requires vs.size() == map.length;
        ensures \result == (\forall int j; 0 <= j && j < n; vs.get(map[j]).boursier && vs.get(map[j]).resident ==>
            // j ≘ rangAppel; map[j] ≘ index in voeuxClasses ≘ rang
            j <= map[j]);
        public static pure model boolean property41a(final LinkedList<VoeuClasse> vs, final int[] map, final int n); @*/

    /*@ requires vs.size() * 100 < Integer.MAX_VALUE; // strictly smaller to enable 1-indexed rang, rangAppel
        requires_redundantly vs.size() < 21_474_836;
        requires (\forall int j; 0 <= j && j < vs.size(); vs.get(j) != null && \invariant_for(vs.get(j)));
        requires (\forall int i1, i2; 0 <= i1 && i1 < vs.size() && 0 <= i2 && i2 < vs.size() && i1 < i2; vs.get(i1).rang < vs.get(i2).rang);
        ensures \result.map.length == vs.size();
        ensures property41b(vs, \result.inv, vs.size()); @*/
    public Permutation calculerOrdreAppel(final LinkedList<VoeuClasse> vs) {

        /*@ // We can always refer to indices instead of rangs:
            assert (\forall int i, j; 0 <= i && i < vs.size() && 0 <= j && j < vs.size();
                i < j <==> vs.get(i).rang < vs.get(j).rang); @*/

        final Queue<Integer> qBR = new LinkedList<>(), qBnR = new LinkedList<>(), qnBR = new LinkedList<>(), qnBnR = new LinkedList<>();

        /*@ loop_invariant 0 <= i && i <= vs.size();
            loop_invariant \invariant_for(qBR) && \invariant_for(qBnR) && \invariant_for(qnBR) && \invariant_for(qnBnR);
            loop_invariant (\forall int j; 0 <= j && j < vs.size(); \invariant_for(vs.get(j)));
            loop_invariant (\forall int j; 0 <= j && j < vs.size(); vs.get(j) != null);

            loop_invariant inRange(vs, qBR) && inRange(vs, qBnR) && inRange(vs, qnBR) && inRange(vs, qnBnR);
            loop_invariant homogenic(vs, qBR, true, true) && homogenic(vs, qBnR, true, false) && homogenic(vs, qnBR, false, true) && homogenic(vs, qnBnR, false, false);

            loop_invariant qBR.size() <= vs.size() && qBnR.size() <= vs.size() && qnBR.size() <= vs.size() && qnBnR.size() <= vs.size();
            loop_invariant qBR.size() + qBnR.size() + qnBR.size() + qnBnR.size() == i;

            loop_invariant (\forall int j; 0 <= j && j < i; occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 1);
            loop_invariant (\forall int j; i <= j && j < vs.size(); occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 0);

            loop_modifies qBR.content, qBnR.content, qnBR.content, qnBnR.content; @*/
        for (int i = 0; i < vs.size(); i++) {
            final VoeuClasse voe = vs.get(i);
            if (voe.boursier) {
                if (voe.resident)
                    qBR.add(i);
                else
                    qBnR.add(i);
            } else {
                if (voe.resident)
                    qnBR.add(i);
                else
                    qnBnR.add(i);
            }
        }

        final int nbBoursiersTotal = qBR.size() + qBnR.size();
        final int nbResidentsTotal = qBR.size() + qnBR.size();

        final int[] map = new int[vs.size()];
        final int[] inv = new int[vs.size()];

        /*@ loop_invariant 0 <= i && i <= vs.size();
            loop_invariant (\forall int j; 0 <= j && j < vs.size(); vs.get(j) != null);
            loop_invariant \invariant_for(map);
            loop_invariant \invariant_for(inv);
            loop_invariant map.length == vs.size() && inv.length == vs.size();
            loop_invariant \invariant_for(qBR) && \invariant_for(qBnR) && \invariant_for(qnBR) && \invariant_for(qnBnR);

            loop_invariant inRange(vs, qBR) && inRange(vs, qBnR) && inRange(vs, qnBR) && inRange(vs, qnBnR);
            loop_invariant homogenic(vs, qBR, true, true) && homogenic(vs, qBnR, true, false) && homogenic(vs, qnBR, false, true) && homogenic(vs, qnBnR, false, false);

            loop_invariant qBR.size() <= vs.size() && qBnR.size() <= vs.size() && qnBR.size() <= vs.size() && qnBnR.size() <= vs.size();

            loop_invariant 0 <= qBR.size() + qBnR.size() && qBR.size() + qBnR.size() <= nbBoursiersTotal;
            loop_invariant 0 <= qBR.size() + qnBR.size() && qBR.size() + qnBR.size() <= nbResidentsTotal;

            loop_invariant i + qBR.size() + qBnR.size() + qnBR.size() + qnBnR.size() == vs.size();

            loop_invariant // index_in_array_or_queue
              (\forall int j; 0 <= j && j < vs.size();
                (occArray(j, map, 0, i) == 0 && occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 1) ||
                (occArray(j, map, 0, i) == 1 && occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 0));

            loop_invariant (\forall int j; 0 <= j && j < i;
              0 <= map[j] && map[j] < map.length);
            loop_invariant (\forall int j; 0 <= j && j < i;
              inv[map[j]] == j);

            loop_invariant (\forall int j; 0 <= j && j < vs.size();
                occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 0 ==>
                (0 <= inv[j] && inv[j] < i));
            loop_invariant (\forall int j; 0 <= j && j < vs.size();
                occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 0 ==>
                map[inv[j]] == j);

            loop_invariant // almost property41b
              (\forall int j; 0 <= j && j < vs.size();
                occQueue(j, qBR) + occQueue(j, qBnR) + occQueue(j, qnBR) + occQueue(j, qnBnR) == 0 ==>
                vs.get(j).boursier && vs.get(j).resident ==>
                inv[j] <= j);
            // loop_invariant property41a(vs, map, i);

            loop_modifies map[*], inv[*];
            loop_modifies qBR.content, qBnR.content, qnBR.content, qnBnR.content; @*/
        for (int i = 0; i < vs.size(); i++) {

            final int boursierRestants = qBR.size() + qBnR.size();
            final int residentsRestants = qBR.size() + qnBR.size();
            final int boursiersAppeles = nbBoursiersTotal - boursierRestants;
            final int residentsAppeles = nbResidentsTotal - residentsRestants;

            final boolean contrainteBoursier = 0 < boursierRestants
                && (boursiersAppeles * 100 < tauxBoursiers * (1 + i));

            /*@ assert contrainteBoursier ==> 0 < qBR.size() || 0 < qBnR.size(); @*/

            final boolean contrainteResident = 0 < residentsRestants
                && (residentsAppeles * 100 < tauxResidents * (1 + i));

            /*@ assert contrainteResident ==> 0 < qBR.size() || 0 < qnBR.size(); @*/

            /*@ nullable @*/ Integer m = null;
            if (!qBR.isEmpty()) {
                /*@ // The assertion is relevant for the non-nullablity of the result of Queue.peek() below and for the condition in the other cases.
                    assert 0 <= qBR._get(0) && qBR._get(0) < vs.size(); @*/
                m = qBR.peek();
            }
            if (!qnBR.isEmpty()) {
                /*@ assert 0 <= qnBR._get(0) && qnBR._get(0) < vs.size(); @*/
                if (!contrainteBoursier && (m == null || m < vs.get(qnBR.peek()).rang))
                    m = qnBR.peek();
            }
            if (!qBnR.isEmpty()) {
                /*@ assert 0 <= qBnR._get(0) && qBnR._get(0) < vs.size(); @*/
                if (!contrainteResident && (m == null || m < vs.get(qBnR.peek()).rang))
                    m = qBnR.peek();
            }
            if (!qnBnR.isEmpty()) {
                /*@ assert 0 <= qnBnR._get(0) && qnBnR._get(0) < vs.size(); @*/
                if (!contrainteBoursier && !contrainteResident && (m == null || m < vs.get(qnBnR.peek()).rang)) {
                    m = qnBnR.peek();
                }
            }
            if (m == null) {
                /*@ assert 0 < qBnR.size();
                    assert 0 <= qBnR._get(0) && qBnR._get(0) < vs.size();  @*/
                m = qBnR.peek();
            }

            final int m1 = m;
            /*@ assert 0 <= m1 && m1 < vs.size();
                assert // some queue
                  (0 < qBR.size() && m == qBR._get(0)) ||
                  (0 < qBnR.size() && m == qBnR._get(0)) ||
                  (0 < qnBR.size() && m == qnBR._get(0)) ||
                  (0 < qnBnR.size() && m == qnBnR._get(0));
                  assert 0 < qBR.size()   && m == qBR._get(0)   ==> vs.get(m).boursier && vs.get(m).resident;
                  assert 0 < qBnR.size()  && m == qBnR._get(0)  ==> vs.get(m).boursier && !vs.get(m).resident;
                  assert 0 < qnBR.size()  && m == qnBR._get(0)  ==> !vs.get(m).boursier && vs.get(m).resident;
                  assert 0 < qnBnR.size() && m == qnBnR._get(0) ==> !vs.get(m).boursier && !vs.get(m).resident;
                assert occQueue(m1, qBR) + occQueue(m1, qBnR) + occQueue(m1, qnBR) + occQueue(m1, qnBnR) == 1; @*/
            x: {
                if (vs.get(m1).boursier) {
                    if (vs.get(m1).resident) {
                        final int m2 = qBR.poll();
                    } else {
                        final int m2 = qBnR.poll();
                    }
                } else {
                    if (vs.get(m1).resident) {
                        final int m2 = qnBR.poll();
                    } else {
                        final int m2 = qnBnR.poll();
                    }
                }
                /*@ assert // shifted_queue
                      (0 < \old(qBR, x).size()   && m == \old(qBR, x)._get(0)   && \old(qBR, x).size() == qBR.size() + 1     && (\forall int j; 0 <= j && j < qBR.size();   qBR._get(j)   == \old(qBR, x)._get(j+1)))  ||
                      (0 < \old(qBnR, x).size()  && m == \old(qBnR, x)._get(0)  && \old(qBnR, x).size() == qBnR.size() + 1   && (\forall int j; 0 <= j && j < qBnR.size();  qBnR._get(j)  == \old(qBnR, x)._get(j+1))) ||
                      (0 < \old(qnBR, x).size()  && m == \old(qnBR, x)._get(0)  && \old(qnBR, x).size() == qnBR.size() + 1   && (\forall int j; 0 <= j && j < qnBR.size();  qnBR._get(j)  == \old(qnBR, x)._get(j+1))) ||
                      (0 < \old(qnBnR, x).size() && m == \old(qnBnR, x)._get(0) && \old(qnBnR, x).size() == qnBnR.size() + 1 && (\forall int j; 0 <= j && j < qnBnR.size(); qnBnR._get(j) == \old(qnBnR, x)._get(j+1)));
                    assert occArray(m1, map, 0, i) == 0;
                    assert (\forall int j; 0 <= j && j < i; map[j] != m1); @*/
                map[i] = m1;
                inv[m1] = i;
                /*@ assert occQueue(m1, qBR) + occQueue(m1, qBnR) + occQueue(m1, qnBR) + occQueue(m1, qnBnR) == 0;
                    assert (\forall int j; 0 <= j && j < vs.size() && j != i; map[j] == \old(map, x)[j]);
                    assert (\forall int j; 0 <= j && j < i; inv[map[j]] == \old(inv, x)[\old(map, x)[j]]); @*/
            }
        }

        return new Permutation(map, inv);
    }
}

public class GroupeClassement__permutation {}
