import java.util.Queue;
import java.util.LinkedList;

public class Test2 {
    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    public void f1(Integer[] a) {

        Queue<Integer> q = new LinkedList<>();

        //@ maintaining q.size()  == \count;
        for (Integer o : a)
            q.add(o);
        //@ assert q.size() == a.length;

        //@ maintaining q.content.theSize >= 0;
        //@ maintaining i + q.content.theSize == a.length;
        //@ loop_modifies q.content.theSize, q.values;
        for (int i = 0; i < a.length; i++) {
            //@ assert !q.isEmpty();
            q.poll();
        }
    }
    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    //@ requires q.size() == a.length;
    public void f2(Integer[] a, Queue<Integer> q) {
        //@ maintaining q.content.theSize >= 0; // really necessary?
        //@ maintaining i + q.content.theSize == a.length;
        //@ loop_modifies q.content.theSize, q.values;
        for (int i = 0; i < a.length; i++) {
            //@ assert !q.isEmpty();
            q.poll();
        }
    }
    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    public void f3(Integer[] a) {

        Queue<Integer> q1 = new LinkedList<>(), q2 = new LinkedList<>();

        //@ maintaining q1.size() + q2.size() == \count;
        for (Integer o : a)
            if (o % 2 == 0)
                q1.add(o);
            else
                q2.add(o);
        //@ assert q1.size() + q2.size() == a.length;

        //@ maintaining q1.content.theSize >= 0;
        //@ maintaining q2.content.theSize >= 0;
        //@ maintaining i + q1.content.theSize + q2.content.theSize == a.length;
        //@ loop_modifies q1.content.theSize, q1.values, q2.content.theSize, q2.values;
        for (int i = 0; i < a.length; i++) {
            //@ assert !q1.isEmpty() || !q2.isEmpty();
            if (!q1.isEmpty())
                q1.poll();
            else
                q2.poll();
        }
    }
    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    public void f4(Integer[] a) {

        Queue<Integer> q1 = new LinkedList<>(), q2 = new LinkedList<>(), q3 = new LinkedList<>(), q4 = new LinkedList<>();

        //@ maintaining q1.size() + q2.size() + q3.size() + q4.size() == \count;
        for (Integer o : a)
            if (o % 4 == 0)
                q1.add(o);
            else if (o % 4 == 1)
                q2.add(o);
            else if (o % 4 == 2)
                q3.add(o);
            else
                q4.add(o);
        //@ assert q1.size() + q2.size() + q3.size() + q4.size() == a.length;

        //@ maintaining i + q1.content.theSize + q2.content.theSize + q3.content.theSize + q4.content.theSize == a.length;
        //@ maintaining q1.content.theSize >= 0 && q2.content.theSize >= 0 && q3.content.theSize >= 0 && q4.content.theSize >= 0;
        //@ loop_modifies q1.content.theSize, q1.values, q2.content.theSize, q2.values, q3.content.theSize, q3.values, q4.content.theSize, q4.values;
        for (int i = 0; i < a.length; i++) {
            //@ assert !q1.isEmpty() || !q2.isEmpty() || !q3.isEmpty() || !q4.isEmpty();
            if (!q1.isEmpty())
                q1.poll();
            else if (!q2.isEmpty())
                q2.poll();
            else if (!q3.isEmpty())
                q3.poll();
            else {
                //@ assert !q4.isEmpty();
                q4.poll();
            }
        }
    }
}
