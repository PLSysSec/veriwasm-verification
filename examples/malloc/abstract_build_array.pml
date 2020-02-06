/*
	To run:
		spin -search -DVECTORSZ=1200 file.pml
	To examine violations:
		spin -t -p -s -r -c file.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "32 word list option" */
#define MAX_LENGTH 50

typedef listoption {
    bool initialized;
 		int lst[MAX_LENGTH];
		int length;
};

/* Functions calls are modelled by sending messages starting and ending a function body.
*/

chan PORT_Alloc_end   = [1] of {listoption};
chan abstract_build_array_end = [1] of {listoption};


/* malloc
	Returns -- nondeterministically -- either an uninitialized result (i.e., a null pointer) or an intialized result with the given length.
*/
proctype Alloc(int newLen){
	listoption new;
	if
	:: new.initialized = true;
		 new.length = newLen;
	:: new.initialized = false;
	fi;
	PORT_Alloc_end!new;
}



proctype abstract_build_array(int n) {
	listoption x;
	int i;

	run Alloc(n);
	PORT_Alloc_end ? x;

	if
	:: !x.initialized ->
		abstract_build_array_end!x;
	:: x.initialized ->
		i = 0;
		do
		:: i < n ->
			x.lst[i] = 0;
			i++;
		:: i >= n -> break; 
		od
		abstract_build_array_end!x;
	fi
}

init {
	int n = 1, i;
	listoption x;

	do
	:: n < 10 -> n++;
	:: break;
	od;

	run abstract_build_array(n);
	abstract_build_array_end?x;

	do
	:: i < n  - 1 -> i++;
	:: break;
	od;
	assert (!x.initialized || x.lst[i] == 0);
}

