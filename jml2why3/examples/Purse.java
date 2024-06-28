class NoCreditException extends Exception {
    public NoCreditException() { }
}

public class Purse {

    private /*@ spec_public @*/ int balance;
    //@ public invariant 0 <= balance;

    /*@ requires true;
      @ assignable \nothing; // Only locations of newly allocated objects
      @ ensures this.balance == 0;
      @*/
    public Purse() {
        balance = 0;
    }

    /*@ requires 0 <= b;
      @ assignable \nothing; // Only locations of newly allocated objects
      @ ensures this.balance == b;
      @*/
    public Purse(int b) {
        balance = b;
    }

    //@ ensures \result == balance;
    public int getBalance() {
        return balance;
    }

    /*@ requires 0 <= s;
      @ requires this.balance + s <= 0x7fff_ffff;
      @ assignable balance;
      @ ensures balance == \old(balance) + s;
      @*/
    public void credit(final int s) {
        balance = balance + s;
    }

    /*@ public behavior
      @   requires 0 <= s;
      @   assignable balance;
      @   ensures s <= \old(balance);
      @   ensures balance == \old(balance) - s;
      @ public exceptional_behavior
      @   requires 0 <= s;
      @   assignable \nothing;
      @   signals (NoCreditException) s > \old(balance) ;
      @*/
    public void withdraw(final int s) throws NoCreditException {
        if (s <= balance)
            this.balance = balance - s;
        else
            throw new NoCreditException();
    }

    /*@ public behavior
      @   requires 0 <= s;
      @   requires dst.balance + s <= 0x7fff_ffff;
      @   assignable balance, dst.balance;
      @   ensures s <= \old(balance);
      @   ensures balance == \old(balance) - s;
      @   ensures dst.balance == \old(dst.balance) + s;
      @ public exceptional_behavior
      @   requires 0 <= s;
      @   assignable \nothing;
      @   signals (NoCreditException) \old(balance) < s;
      @*/
    public void transfer(final Purse dst, final int s) throws NoCreditException {
        withdraw(s);
        dst.credit(s);
    }

    //@ ensures \result == 42;
    int test1() {
        Purse p = new Purse();
        p.credit(42);
        return p.balance;
    }

    //@ requires 0 <= initial;
    //@ requires 0 <= amount;
    //@ requires initial + amount + 1 <= 0x7fff_ffff;
    boolean test2(final int initial, int amount) {
        Purse purse = new Purse(initial);
        try {
            amount = amount + 1;
            purse.withdraw(amount);
            return true;
        } catch (NoCreditException e) {
            return false;
        }
    }
}
