package bankaccount; public class Account {
	final int OVERDRAFT_LIMIT = 0;

	//@ invariant balance >= OVERDRAFT_LIMIT;
int balance = 0;

	/*@ 
	 ensures balance == 0; @*/
	Account() {
	}

	/*@ 
	 ensures (!\result ==> balance == \old(balance)) 
	  && (\result ==> balance == \old(balance) + x); @*/
	boolean update(int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 ensures (!\result ==> balance == \old(balance)) 
	  && (\result ==> balance == \old(balance) - x); @*/
	boolean undoUpdate(int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	final static int INTEREST_RATE = 2;

	int interest = 0;

	/*@ 
	 ensures (balance >= 0 ==> \result >= 0) 
	   && (balance <= 0 ==> \result <= 0); @*/
	 /*@pure@*/  int calculateInterest() {
		return balance * INTEREST_RATE / 36500;
	}


}
