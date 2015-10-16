package bankaccount; public class Application {
	//@ invariant account != null;
Account account = new Account();

	/*@ 
	 requires true; @*/
	 private void  nextDay__wrappee__BankAccount  () {
	}

	/*@ 
	 ensures account.withdraw == 0; @*/
	void nextDay() {
		nextDay__wrappee__BankAccount();
		account.withdraw = 0;
	}


	void nextYear() {
	}


}
