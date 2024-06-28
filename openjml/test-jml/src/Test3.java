public class Test3 {
    //@ requires (\forall int i; 0 <= i && i < voeuxClasses.length; voeuxClasses[i] != null);
    public Object[] ordreAppel(Object[] voeuxClasses) {

        Queue<Object> BR = new LinkedList<>();

        //@ maintaining 0 <= i;
        //@ maintaining BR.content.theSize == i;
        //@ loop_modifies i, BR.content.theSize, BR.values;
        for (int i=0; i<voeuxClasses.length; i++) {
            BR.add(voeuxClasses[i]);
        }

        Object[] ordreAppel = new Object[voeuxClasses.length];

        //@ maintaining (\forall int i; 0 <= i && i < ordreAppel.length; ordreAppel[i] == null <==> nbAppeles <= i);
        //@ loop_modifies nbAppeles;
        for (int nbAppeles = 0; nbAppeles < ordreAppel.length; nbAppeles++) {
            //@ assert 1==1;
        }

        return ordreAppel;
    }
}
