//@ model import java.util.Arrays;

/** Keep a copy of the initial array. */
class P<E> {

    //@ ghost E[] a0;     // Original array
    //@ ghost int[] ix;   // Indices of values in original array: an array is a permutation iff. a[i] == a0[ix[i]]
    //@ ghost int[] ixix; // Indices of indices in ix: ix[ixix[i]] == i
    //@ model int N; represents N = ix.length;

    //@ invariant N == a0.length && N == ixix.length && ix != ixix;
    //@ invariant (\forall int i; 0 <= i && i < N; 0 <= ix[i] && ix[i] < N);
    //@ invariant (\forall int i; 0 <= i && i < N; 0 <= ixix[i] && ixix[i] < N);
    //@ invariant (\forall int i; 0 <= i && i < N; ix[ixix[i]] == i);
    //@ invariant (\forall int i; 0 <= i && i < N; ixix[ix[i]] == i);

    //@ assignable \nothing; // I.e., only locations of newly allocated objects
    //@ ensures N == a.length && a0 != a;
    //@ ensures (\forall int i; 0 <= i && i < N; a0[i] == a[i]);
    //@ ensures (\forall int i; 0 <= i && i < N; ix[i] == i);
    //@ ensures (\forall int i; 0 <= i && i < N; ixix[i] == i);
    P(E[] a) {
        //@ set a0 = Arrays.copyOf(a, a.length);
        //@ set ix = new int[a.length];
        //@ set ixix = new int[a.length];
        //@ loop_invariant 0 <= n && n <= a.length;
        //@ loop_invariant (\forall int i; 0 <= i && i < n; a0[i] == a[i] && ix[i] == i && ixix[i] == i);
        for (int n = 0; n < a.length; n++) {
            //@ set ix[n] = n;
            //@ set ixix[n] = n;
        }
    }

    //@ requires a.length == N && a != a0;
    //@ requires 0 <= n && n < N && 0 <= m && m < N;
    //@ requires (\forall int i; 0 <= i && i < N; a[i] == a0[ix[i]]);
    //@ assignable a[n], a[m], ix[n], ix[m], ixix[ix[n]], ixix[ix[m]];
    //@ ensures a[m] == \old(a[n]) && a[n] == \old(a[m]);
    //@ ensures (\forall int i; 0 <= i && i < N; a[i] == a0[ix[i]]);
    void swap(E[] a, int n, int m) {
        /*@ nullable */ E x = a[n];
        a[n] = a[m];
        a[m] = x;
        //@ ghost int i = ix[n];
        //@ ghost int j = ix[m];
        //@ set ix[n] = j;
        //@ set ix[m] = i;
        //@ set ixix[j] = n;
        //@ set ixix[i] = m;
    }

    //@ requires a.length == 3;
    //@ ensures \result.N == a.length;
    //@ ensures (\forall int i; 0 <= i && i < a.length; \result.a0[i] == \old(a[i]));
    //@ ensures (\forall int i, j; 0 <= i && i < a.length && j == \result.ix[i]; a[i] == \old(a[j]));
    // i.e., (\forall int i; 0 <= i && i < a.length; a[i] == \old(a[\result.ix[i]]));
    static P<Integer> test(Integer[] a) {
        P<Integer> p = new P<>(a);
        p.swap(a, 1, 2);
        return p;
    }
}
