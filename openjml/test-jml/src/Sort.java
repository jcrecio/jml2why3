public class Sort {

    class T {
        final int rang;
        T(int rang) {
            this.rang = rang;
        }
    }

    //@ requires \nonnullelements(a); // requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    //@ assignable a[*];
    //@ ensures (\forall int i, j; 0 < i && i <= j && j < a.length; a[i].rang <= a[j].rang);
    //@ ensures \result.N == a.length;
    //@ ensures (\forall int i; 0 <= i && i < a.length; \result.a0[i] == \old(a[i]));
    //@ ensures (\forall int i, j; 0 <= i && i < a.length && j == \result.ix[i]; a[i] == \old(a[j]));
    P<T> selectionSort(T[] a) {
        P<T> res = new P<>(a);
        int min = 0;
        //@ loop_invariant 0 <= n && n <= a.length;
        //@ loop_invariant (\forall int i1, i2; 0 <= i1 && i1 <= i2 && i2 < n; a[i1].rang <= a[i2].rang);
        //@ loop_invariant (\forall int i1, i2 ; 0 <= i1 && i1 < n && n <= i2 && i2 < a.length; a[i1].rang <= a[i2].rang);
        //@ loop_invariant \invariant_for (res);
        //@ loop_invariant (\forall int i; 0 <= i && i < a.length; res.a0[i] == \pre(a[i]));
        //@ loop_invariant (\forall int i, j; 0 <= i && i < a.length && j == res.ix[i]; a[i] == \pre(a[j]));
        //@ loop_modifies a[*], res.ix[*], res.ixix[*];
        for (int n = 0; n < a.length; n++) {
            min = n;
            //@ loop_invariant n < m && m <= a.length;
            //@ loop_invariant n <= min && min < m;
            //@ loop_invariant (\forall int i; n <= i && i < m; a[min].rang <= a[i].rang);
            //@ loop_modifies min;
            for (int m = n + 1; m < a.length; m++)
                if (a[m].rang < a[min].rang)
                    min = m;
            if (min != n)
                res.swap(a, min, n);
        }
        return res;
    }

    //@ requires \nonnullelements(a); // requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    //@ assignable a[*];
    //@ ensures (\forall int i, j; 0 < i && i <= j && j < a.length; a[i].rang <= a[j].rang);
    //@ ensures \result.N == a.length;
    //@ ensures (\forall int i; 0 <= i && i < a.length; \result.a0[i] == \old(a[i]));
    //@ ensures (\forall int i, j; 0 <= i && i < a.length && j == \result.ix[i]; a[i] == \old(a[j]));
    P<T> bubbleSort(T[] a) {
        P<T> res = new P<>(a);
        if (0 < a.length) {
            //@ loop_invariant 0 <= n && n <= a.length-1;
            //@ loop_invariant (\forall int i1, i2; n <= i1 && i1 <= i2 && i2 < a.length; a[i1].rang <= a[i2].rang);
            //@ loop_invariant (\forall int i1, i2; 0 <= i1 && i1 <= n && n < i2 && i2 < a.length; a[i1].rang <= a[i2].rang);
            //@ loop_invariant \invariant_for (res);
            //@ loop_invariant (\forall int i; 0 <= i && i < a.length; res.a0[i] == \pre(a[i]));
            //@ loop_invariant (\forall int i, j; 0 <= i && i < a.length && j == res.ix[i]; a[i] == \pre(a[j]));
            //@ loop_modifies a[*], res.ix[*], res.ixix[*];
            for (int n = a.length-1; 0 < n; n--) {
                //@ loop_invariant 0 <= m && m <= n;
                //@ loop_invariant (\forall int i1, i2; n <= i1 && i1 <= i2 && i2 < a.length; a[i1].rang <= a[i2].rang);
                //@ loop_invariant (\forall int i1, i2; 0 <= i1 && i1 <= n && n < i2 && i2 < a.length; a[i1].rang <= a[i2].rang);
                //@ loop_invariant (\forall int i; 0 <= i && i <= m; a[i].rang <= a[m].rang);
                //@ loop_invariant \invariant_for (res);
                //@ loop_invariant (\forall int i; 0 <= i && i < a.length; res.a0[i] == \pre(a[i]));
                //@ loop_invariant (\forall int i, j; 0 <= i && i < a.length && j == res.ix[i]; a[i] == \pre(a[j]));
                //@ loop_modifies a[0..n-1], res.ix[0..n-1], res.ixix[*];
                for (int m = 0; m < n; m++)
                    if (a[m].rang > a[m+1].rang)
                        res.swap(a, m, m+1);
            }
        }
        return res;
        // Feasibility is provable but will take a while. Don't give up!
    }
}
