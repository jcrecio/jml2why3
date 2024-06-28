import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;

//public class Test {
//void f(boolean a, boolean b, Collection<Object> c) {
//	  // assert (a && b ==> c == null); // fails
//	  //@ assert (a && b ==> this == null); // works
//
//	  // assert (a  && b ==> !c.isEmpty()); // fails
//	  //@ assert (a  ==> !c.isEmpty()); // works
//
//	  // assert ((a && b && !c.isEmpty()) ==> !c.isEmpty()); // fails
//	  //@ assert ((a && b && !c.isEmpty()) ==> 0 < c.size()); // works
//	}
//}

//public class Test {
//	public void f(Object o) {
//		Map<Object, Object> m = new HashMap<>();
//		m.put(o, o);
//		//@ assert o != null;
//	}
//}

//public class Test {
////@ requires \forall int i; 0 <= i && i < a.length; \typeof(a[i]) <: \type(Comparable<Object>);
//	void f(Object[] a) {
//		Arrays.sort(a);
//		// @ assert a != null;
//		Arrays.sort(a, (Object o1, Object o2) -> 0);
//		// @ assert a != null;
//	}
//}

//public class Test {
//	// @ requires a.length == q1.size() + q2.size();
//	// @ requires q1 != q2;
//	public void f1(Integer[] a, Queue<Integer> q1, Queue<Integer> q2) {
//		// @ maintaining i + q1.size() + q2.size()== a.length;
//		for (int i = 0; i < a.length; i++) {
//			// @ assert !q1.isEmpty() || !q2.isEmpty();
//			if (!q1.isEmpty())
//				q1.poll();
//			else if (!q2.isEmpty())
//				q2.poll();
//		}
//	}
//
//	//@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
//	public void f2(Integer[] a) {
//
//		Queue<Integer> q1 = new LinkedList<>(), q2 = new LinkedList<>();
//
//		// @ maintaining q1.size() + q2.size() == \count;
//		for (Integer o : a) {
//			if (o % 2 == 0)
//				q1.add(o);
//			else
//				q2.add(o);
//		}
//		// @ assert q1.size() + q2.size() == a.length;
//		// @ maintaining i + q1.size() + q2.size() == a.length;
//		// loop_modifies q1.content.theSize, q2.content.theSize;
//		for (int i = 0; i < a.length; i++) {
//			// @ assert !q1.isEmpty() || !q2.isEmpty();
//			if (!q1.isEmpty())
//				q1.poll();
//			else if (!q2.isEmpty())
//				q2.poll();
//		}
//	}
//}

//public class Test {
//	void f1(Queue<Integer> q) {
//		//@ loop_modifies q.content.*;
//		// loop_modifies q.content.size; // works
//		while (!q.isEmpty())
//			q.poll();
//	}
//}

public class Test {
    //    class Integer {
    //
    //        public final int rang;
    //        public final boolean estBoursier;
    //        public final boolean estResident;
    //        public int rangAppel = -1;
    //
    //        public Integer(int rang, boolean estBoursier, boolean estResident) {
    //            this.rang = rang;
    //            this.estBoursier = estBoursier;
    //            this.estResident = estResident;
    //        }
    //    }
    //	//@ requires voeuxClasses.length == BR.size() + BnR.size() + nBR.size() + nBnR.size();
    //    //@ requires BR != BnR && BR != nBR && BR != nBnR && BnR != nBR && BnR != nBnR && nBR != nBnR;
    //	public void f1(Integer[] voeuxClasses, Queue<Integer> BR, Queue<Integer> BnR, Queue<Integer> nBR, Queue<Integer> nBnR) {
    //        //@ maintaining nbAppeles + BR.size() + BnR.size() + nBR.size() + nBnR.size() == voeuxClasses.length;
    //        for (int nbAppeles = 0; nbAppeles < voeuxClasses.length; nbAppeles++) {
    //        	//@ assert !BR.isEmpty() || !BnR.isEmpty() || !nBR.isEmpty() || !nBnR.isEmpty();
    //        	if (!BR.isEmpty())
    //        		BR.poll();
    //        	else if (!BnR.isEmpty())
    //        		BnR.poll();
    //        	else if (!nBR.isEmpty())
    //        		nBR.poll();
    //        	else if (!nBnR.isEmpty())
    //        		nBnR.poll();
    //        }
    //	}

    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    public void f2(Integer[] a) {

        Queue<Integer> q1 = new LinkedList<>(), q2 = new LinkedList<>();

        // @ maintaining q1.size() + q2.size() == \count;
        for (Integer o : a) {
            if (o % 2 == 0)
                q1.add(o);
            else
                q2.add(o);
        }
        // @ assert q1.size() + q2.size() == a.length;

        // @ maintaining i + q1.size() + q2.size() == a.length;
        // loop_modifies q1.content.theSize, q2.content.theSize;
        for (int i = 0; i < a.length; i++) {
            // @ assert !q1.isEmpty() || !q2.isEmpty();
            if (!q1.isEmpty())
                q1.poll();
            else if (!q2.isEmpty())
                q2.poll();
        }
    }
    //@ requires (\forall int i; 0 <= i && i < a.length; a[i] != null);
    public void f1(Integer[] a) {

        Queue<Integer> q1 = new LinkedList<>(), q2 = new LinkedList<>();

        //@ maintaining q1.size() + q2.size()  == \count;
        for (Integer o : a) {
            if (o % 2 == 0)
                q1.add(o);
            else
                q2.add(o);
        }
        //@ assert q1.size() + q2.size()== a.length;

        //@ maintaining i + q1.size() + q2.size()  == a.length;
        // loop_modifies q1.content.theSize, q2.content.theSize;
        for (int i = 0; i < a.length; i++) {
            //@ assert !q1.isEmpty() || !q2.isEmpty() ;
            if (!q1.isEmpty())
                q1.poll();
            else if (!q2.isEmpty())
                q2.poll();
        }
    }
}
