/*
	To run:
		spin -search file.pml
	To examine violations:
		spin -t -p -s -r -c file.pml

	There should be no assertion violations and no invalid end states.
*/




/* Functions calls are modelled by sending messages starting and ending a function body.
*/
chan pow2_start = [1] of {int};
chan pow2_end = [1] of {int};

active proctype pow2() {
	/* receive the buffer as a parameter */
	int i, a, n;
end:
	do :: pow2_start?n ->
		i = 0;
		a = 1;
		do
		:: i < n ->
			i++;
			a = a * 2;
		:: i >= n -> break;
		od;
		pow2_end!a;
	od;
}

init {
	int n = 4, ret;
	pow2_start!n;
	pow2_end?ret;
	assert (ret == 2^n);
}

