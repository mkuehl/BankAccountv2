package bankaccount; public class Application {
	//@ invariant account != null;
Account account = new Account();

	/*@ 
	 requires true; @*/
	 private void  nextDay__wrappee__BankAccount  () {
	}

	/*@ 
	 ensures true 
	  && (account.balance >= 0 ==> account.interest >= \old(account.interest)) 
	  && (account.balance <= 0 ==> account.interest <= \old(account.interest)); @*/
	void nextDay() {
		nextDay__wrappee__BankAccount();
		account.interest += account.calculateInterest();
	}


	 private void  nextYear__wrappee__BankAccount  () {
	}

	/*@ 
	 ensures account.balance == \old(account.balance) + \old(account.interest) 
	  && account.interest == 0; @*/
	void nextYear() {
		nextYear__wrappee__BankAccount();
		account.balance += account.interest;
		account.interest = 0;
	}


}
