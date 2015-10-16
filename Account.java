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
	 private boolean  update__wrappee__BankAccount  (int x) {
		int newBalance = balance + x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 ensures ( (!\result ==> balance == \old(balance)) 
	  && (\result ==> balance == \old(balance) + x) ) 
	  && (!\result ==> withdraw == \old(withdraw)) 
	  && (\result ==> withdraw <= \old(withdraw)); @*/
	boolean update(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw += x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!update__wrappee__BankAccount(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}

	/*@ 
	 ensures (!\result ==> balance == \old(balance)) 
	  && (\result ==> balance == \old(balance) - x); @*/
	 private boolean  undoUpdate__wrappee__BankAccount  (int x) {
		int newBalance = balance - x;
		if (newBalance < OVERDRAFT_LIMIT)
			return false;
		balance = newBalance;
		return true;
	}

	/*@ 
	 ensures ( (!\result ==> balance == \old(balance)) 
	  && (\result ==> balance == \old(balance) - x) ) 
	  && (!\result ==> withdraw == \old(withdraw)) 
	  && (\result ==> withdraw >= \old(withdraw)); @*/
	boolean undoUpdate(int x) {
		int newWithdraw = withdraw;
		if (x < 0)  {
			newWithdraw -= x;
			if (newWithdraw < DAILY_LIMIT) 
				return false;
		}
		if (!undoUpdate__wrappee__BankAccount(x))
			return false;
		withdraw = newWithdraw;
		return true;
	}

	final static int DAILY_LIMIT = -1000;

	//@ invariant withdraw >= DAILY_LIMIT;
int withdraw = 0;


}
