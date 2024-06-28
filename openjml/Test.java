import java.util.Queue;
import java.util.LinkedList;

class C {
    boolean flag;
}

class QueueArray {
    public final C[] values;
    public int first, end;

    /*@ public invariant first <= end;
        public invariant 0 <= end <= values.length;
        public invariant 0 <= first <= values.length;
        public invariant (\forall int i; first <= i && i < end; values[i] != null);
     @*/

    /*@ requires 0 <= capacity;
        ensures first == 0 && end == 0 && values.length == capacity;
        ensures_redundantly 0 == size();
      @*/
    public QueueArray(int capacity) {
        values = new C[capacity];
        first = 0;
        end = 0;
    }

    /*@ ensures \result == end - first;
        ensures 0 <= \result;
      @*/
    public /*@ pure @*/ int size() {
        return end - first;
    }

    /*@ requires 0 <= i && i < size();
        ensures \result == values[first+i];
        public pure model C _get(int i);
      @*/

    /*@ requires end < values.length;
        ensures end == \old(end) + 1;
        ensures (\forall int i; first <= i && i < \old(end); values[i] == \old(values)[i]);
        ensures values[\old(end)] == o;
        ensures \result;
        // And to void a PossiblyBadArrayAssignment according to https://github.com/OpenJML/OpenJML/issues/628#issuecomment-407996574:
        requires \type(C) <: \elemtype(\typeof(values));
      @*/
    public boolean add(C o) {
        values[end++] = o;
        return true;
    }

    /*@ public behavior
          requires 0 < size();
          ensures \result == values[first];
        also
        public behavior
          requires 0 == size();
          ensures \result == null;
      @*/
    public /*@ pure nullable @*/ C peek() {
        if (0 < size()) {
            //@ assert 0 < size();
            //@ assert first < end;
            //@ assert first < values.length;
            //@ assert 0 <= first && first < values.length;
            return values[first];
        } else {
            //@ assert 0 == size();
            return null;
        }
    }

    /*@ public behavior
          requires 0 < size();
          ensures first == \old(first) + 1;
          ensures \result == values[\old(first)];
          writes first;
        also public behavior
          requires 0 == size();
          ensures \result == null;
      @*/
    public /*@ nullable @*/ C pop() {
        if (0 < size())
            return values[first++];
        else {
            //@ assert 0 == size();
            return null;
        }
    }
}

public class Test {

    // Using a poor man's queue

    //@ requires \nonnullelements(a);
    int f1(C[] a) {
        C[] q1 = new C[a.length];
        int q1size = 0;
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant 0 <= q1size && q1size <= i;
            loop_invariant (\forall int j; 0 <= j && j < q1size; q1[j].flag);
            loop_modifies i, q1[*], q1size;
          @*/
        for (int i=0; i<a.length; i++) {
            if (a[i].flag) {
                q1[q1size++] = a[i];
            }
        }
        return q1size;
    }

    //@ requires \nonnullelements(a);
    int f2(C[] a) {
        C[] q1 = new C[a.length], q2 = new C[a.length];
        int q1size = 0, q2size = 0;
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant q1size + q2size == i;
            loop_invariant 0 <= q1size && q1size <= i;
            loop_invariant 0 <= q2size && q2size <= i;
            loop_invariant (\forall int j; 0 <= j && j < q1size;  q1[j].flag);
            loop_invariant (\forall int j; 0 <= j && j < q2size; !q2[j].flag);
            loop_modifies i, q1[*], q2[*], q1size, q2size;
          @*/
        for (int i=0; i<a.length; i++) {
            if (a[i].flag) {
                q1[q1size++] = a[i];
            } else {
                q2[q2size++] = a[i];
            }
        }
        return q1size + q2size;
    }

    // Using an array queue

    //@ requires \nonnullelements(a);
    int f3(C[] a) {
        QueueArray q1 = new QueueArray(a.length);
        //@ assume a != q1.values;
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant a != q1.values;
            loop_invariant 0 <= q1.end && q1.end <= i;
            loop_invariant \nonnullelements(a);
            loop_invariant \invariant_for(q1);
            loop_invariant (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            loop_modifies q1.values[*], q1.end;
          @*/
        for (int i=0; i<a.length; i++) {
            C o = a[i];
            x: if (o.flag) {
                //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
                //@ assume \type(C) <: \elemtype(\typeof(q1.values));
                q1.add(o);
                //@ assert (\forall int j; 0 <= j && j < \old(q1, x).size(); \old(q1, x)._get(j).flag);
                //@ assert (\forall int j; 0 <= j && j < q1.size()-1; q1._get(j).flag);
                //@ assert q1._get(q1.size()-1).flag;
                //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            } else {
                //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            }
            //@ assert (\forall int j; 0 <= j && j < \old(q1, x).size(); \old(q1, x)._get(j).flag);
            //@ assert (\forall int j; 0 <= j && j < q1.size()-1; q1._get(j).flag);
            //@ assert q1._get(q1.size()-1).flag;
            //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
        }
        return q1.size();
    }

    //@ requires \nonnullelements(a);
    int f4(C[] a) {
        QueueArray q1 = new QueueArray(a.length), q2 = new QueueArray(a.length);
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant \nonnullelements(a);
            loop_invariant \invariant_for(q1) && \invariant_for(q2);
            loop_invariant (\forall int j; 0 <= j && j < q1.size();  q1._get(j).flag);
            loop_invariant (\forall int j; 0 <= j && j < q2.size(); !q2._get(j).flag);
            loop_modifies i, q1.values[*], q2.values[*], q1.end, q2.end;
          @*/
        for (int i=0; i<a.length; i++) {
            if (a[i].flag) {
                q1.add(a[i]);
            } else {
                q2.add(a[i]);
            }
        }
        return q1.size() + q2.size();
    }

    // Using a real queue

    //@ requires \nonnullelements(a);
    int f5(C[] a) {
        Queue<C> q1 = new LinkedList<>();
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant \nonnullelements(a);
            loop_invariant \invariant_for(q1);
            loop_invariant (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            loop_modifies q1.*;
          @*/
        for (int i=0; i<a.length; i++) {
            x: if (a[i].flag) {
                q1.add(a[i]);
                //@ assume (q1._get(q1.size()-1).flag);
                //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            } else {
                //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
            }
            //@ assert (\forall int j; 0 <= j && j < q1.size(); q1._get(j).flag);
        }
        return q1.size();
    }

    //@ requires \nonnullelements(a);
    int f6(C[] a) {
        Queue<C> q1 = new LinkedList<>(), q2 = new LinkedList<>();
        //@ set q1.containsNull = false;
        //@ set q2.containsNull = false;
        /*@ loop_invariant 0 <= i && i <= a.length;
            loop_invariant \invariant_for(q1) && \invariant_for(q2);
            loop_invariant (\forall int j; 0 <= j && j < q1.size();  q1._get(j).flag);
            loop_invariant (\forall int j; 0 <= j && j < q2.size(); !q2._get(j).flag);
            loop_modifies i, q1.content, q2.content; @*/
        for (int i=0; i<a.length; i++) {
            if (a[i].flag) {
                q1.add(a[i]);
                /*@ assume q1._get(q1.size()-1) == a[i];
                    assert (\forall int j; 0 <= j && j < q1.size();  q1._get(j).flag);
                    assert (\forall int j; 0 <= j && j < q2.size();  !q2._get(j).flag); @*/
            } else {
                q2.add(a[i]);
                /*@ assume q2._get(q2.size()-1) == a[i];
                    assert (\forall int j; 0 <= j && j < q1.size();  q1._get(j).flag);
                    assert (\forall int j; 0 <= j && j < q2.size(); !q2._get(j).flag); @*/
            }
            /*@ assert (\forall int j; 0 <= j && j < q1.size();  q1._get(j).flag);
                assert (\forall int j; 0 <= j && j < q2.size(); !q2._get(j).flag); @*/
            /*@ assume q1.content != null;
                assume q2.content != null;
                set q1.content.owner = q1;
                set q2.content.owner = q2; @*/
        }
        return q1.size() + q2.size();
    }
}
