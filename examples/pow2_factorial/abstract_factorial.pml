/*
	To run:
		spin -search file.pml
	To examine violations:
		spin -t -p -s -r -c file.pml

	There should be no assertion violations and no invalid end states.
*/

/* Functions calls are modelled by sending messages starting and ending a function body.
*/

chan abstract_factorial_end   = [1] of {int};


proctype abstract_factorial(int n) {
	int i = n, ret;

	do
	:: i > 0 ->
		i--;
	:: i <= 0 -> break;
	od;
	ret = 1;
	do
	:: n > i ->
		ret = ret * (i+1);
		i++;
	:: n <= i -> break;
	od;
	abstract_factorial_end!ret;
}

/* The normal recursive C code implementation of factorial */
c_code { 
	int fact(int n) {
		int i, fact = 1;
		for (i = 1; i <= n; i++)
	    fact = fact * i;
		return fact;
	}
};

int x;

init {
	int ret, m;
	/* Pick a number between 0 and 15 */
	m = 0;
	do
	:: m < 15 -> m++;
	:: break;
	od;

	c_code {
		now.x = fact(Pinit->m);
	};

	run abstract_factorial(m);
	abstract_factorial_end?ret;

	/* Compare the result with the C implementation */
	assert(c_expr {Pinit->ret == now.x});
}

