//@ model import java.util.Arrays;

/** Only the indices, no copy of the initial array. */
class P2<E> {

    //@ public ghost final int[] ix;
    //@ model int N; represents N = ix.length;

    //@ ensures \result == (a0.length == N && a.length == N && 0 <= n && n <= N && (\forall int i; 0 <= i && i < n; a[i] == a0[ix[i]]));
    //@ pure model boolean isPermutation(E[] a0, E[] a, int n);

    //@ assignable \nothing; // I.e., only locations of newly allocated objects
    //@ ensures this.N == N;
    //@ ensures (\forall E[] a; a.length == N; isPermutation(a, a, N);
    P2(int N);

    //@ requires a.length == N && 0 <= n && n < N && 0 <= m && m < N;
    //@ assignable a[n], a[m], ix[n], ix[m];
    //@ ensures a[m] == \old(a[n]) && a[n] == \old(a[m]);
    //@ ensures ix[n] == \old(ix[m]) && ix[m] == \old(ix[n]);
    //@ ensures (\forall E[] a0; a0.length == N; \old(isPermutation(a0, a, N)) ==> isPermutation(a0, a, N));
    void swap(E[] a, int n, int m);


    // //@ requires a.length == N;
    // //@ requires 0 <= n && n < N && 0 <= m && m < N;
    // //@ ensures (\forall E[] a0; a.length == N; isPermutation(a0, ))
    // //@ requires (\forall int i; 0 <= i && i < N; a[i] == a0[ix[i]]);
    // // requires (\forall int i, j; 0 <= i && i < N && j == ix[i]; a[i] == a0[j]);
    // //@ assignable a[n], a[m], ix[n], ix[m];
    // //@ ensures a[m] == \old(a[n]) && a[n] == \old(a[m]);
    // //@ ensures ix[n] == \old(ix[m]) && ix[m] == \old(ix[n]);
    // //@ ensures (\forall int i; 0 <= i && i < N; a[i] == a0[ix[i]]);
    // // ensures (\forall int i, j; 0 <= i && i < N && j == ix[i]; a[i] == a0[j]);
    // void swap(E[] a, int n, int m) {
    //     /*@ nullable */ E x = a[n];
    //     a[n] = a[m];
    //     a[m] = x;
    //     //@ ghost int y = ix[n];
    //     //@ set ix[n] = ix[m];
    //     //@ set ix[m] = y;
    // }

    // //@ requires 3 < a.length;
    // //@ ensures \result.N == a.length;
    // //@ ensures (\forall int i; 0 <= i && i < a.length; \result.a0[i] == \old(a[i]));
    // //@ ensures (\forall int i, j; 0 <= i && i < a.length && j == \result.ix[i]; a[i] == \old(a[j]));
    // // i.e., (\forall int i; 0 <= i && i < a.length; a[i] == \old(a[\result.ix[i]]));
    // static P<Integer> test(Integer[] a) {
    //     P<Integer> p = new P<>(a);
    //     p.swap(a, 1, 2);
    //     return p;
    // }
}
