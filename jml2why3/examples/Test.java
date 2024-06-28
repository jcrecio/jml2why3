import java.util.Map;
import java.util.HashMap;
import java.util.Queue;
import java.util.PriorityQueue;
import java.util.LinkedList;

class V {

    public final boolean estBoursier;
    public final boolean estResident;
    public final int rang;
    public int rangAppel = -1;

    //@ invariant 0 <= rang && rang <= Integer.MAX_VALUE;

    //@ requires 0 <= rang && rang <= Integer.MAX_VALUE;
    public V(final int rang, final boolean estBoursier, final boolean estResident) {
        this.rang = rang;
        this.estBoursier = estBoursier;
        this.estResident = estResident;
    }

    //@ ensures \result == (estBoursier == other.estBoursier && estResident == other.estResident && rang == other.rang);
    //@ pure model public boolean eq(final V other);
}

class Test {

    //@ requires v1.eq(v2);
    //@ requires v2.eq(v3);
    //@ ensures v1.eq(v3);
    void testEq(final V v1, final V v2, final V v3) {}

    //@ ensures \result == v;
    V test1(final V v) {
        return v;
    }
    //@ ensures \result == v;
    V test2(final V v) {
        v.rangAppel = 42;
        return v;
    }

    //@ requires \nonnullelements(a);
    //@ ensures \result.length == a.length;
    //@ ensures \nonnullelements(\result);
    //@ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == a[i]);
    V[] test3(final V[] a) {
        final V[] b = new V[a.length];
        //@ loop_invariant (\forall int j; 0 <= j && j < i; b[j] == a[j]);
        for (int i=0; i < a.length; i++) {
            b[i] = a[i];
        }
        return b;
    }

    //@ requires \nonnullelements(a);
    //@ requires 0 < a.length;
    void test4(final V[] a) {
        final Queue<V> q = new LinkedList<>();
        final V v = a[0];
        q.add(v);
        //@ assert q._get(0) == a[0];
    }

    //@ requires 0 != q.content.theSize;
    //@ ensures \result == \old(q)._get(0);
    V test5a(final Queue<V> q) {
        final V v = q.poll();
        return v;
    }

    //@ requires q.content.theSize <= Integer.MAX_VALUE;
    //@ ensures \result.length == \old(q.content.theSize);
    //@ ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == \old(q._get(i)));
    V[] test5b(final Queue<V> q) {
        final int n = q.size();
        final V[] res = new V[n];
        //@ loop_invariant n == q.content.theSize + i;
        //@ loop_invariant (\forall int j; 0 <= j && j < q.content.theSize; q._get(j) == \old(q)._get(j+i));
        //@ loop_invariant (\forall int j; 0 <= j && j < i; res[j] == \old(q)._get(j));
        for (int i = 0; i < n; i++) {
            res[i] = q.poll();
        }
        return res;
    }

    //@ requires \nonnullelements(a);
    //@ ensures (\forall int i; 0 <= i && i < a.length; \result[i] == a[i]);
    V[] test6(final V[] a) {
        final Queue<V> q = new LinkedList<>();
        //@ loop_invariant q.content.theSize == i;
        //@ loop_invariant (\forall int j; 0 <= j && j < q.content.theSize; q._get(j) == a[j]);
        for (int i=0; i<a.length; i++) {
            final V x = a[i];
            q.add(x);
        }

        start: {
            final V[] res = new V[a.length];
            //@ loop_invariant a.length == q.content.theSize + i;
            //@ loop_invariant (\forall int j; 0 <= j && j < q.content.theSize; q._get(j) == \old(q, start)._get(j+i));
            //@ loop_invariant (\forall int j; 0 <= j && j < q.content.theSize; q._get(j) == a[j+i]);
            //@ loop_invariant (\forall int j; 0 <= j && j < i; res[j] == a[j]);
            for (int i=0; i<a.length;i++) {
                res[i] = q.poll();
            }
            return res;
        }
    }
}
