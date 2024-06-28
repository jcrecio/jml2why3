class Test4 {
    //@ ensures \result == (a == b);
    //@ pure model boolean isEqual(int a, int b);

    //@ requires isEqual(a, b);
    //@ ensures \result == 0;
    int f1(int a, int b) {
        return a - b;
    }

    //@ ensures \result == (\forall int i; 0 <= i && i < a.length; a[i] == 0);
    //@ pure model boolean onlyZeros(int[] a);

    //@ requires onlyZeros(a);
    //@ ensures \result == 0;
    int f2(int[] a) {
        int res = 0;
        //@ loop_invariant 0 <= i && i <= a.length;
        //@ loop_invariant res == 0;
        for (int i=0; i < a.length; i++) {
            res += a[i];
        }
        return res;
    }
}
