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

chan abstract_strncmp_start = [1] of {listoption, listoption};
chan abstract_strncmp_end   = [1] of {int};


proctype abstract_strncmp(int count0) {
	listoption x, y;
	int count, cs, ct, ret = 0;
	byte c1, c2;
	bool retd, breaked;

	abstract_strncmp_start?(x, y);
	count = count0;
	cs = 0;
	ct = 0;
	retd = false;
	breaked = false;
	do 
	:: count != 0 && !breaked && ! retd ->
		c1 = x.lst[cs];
		c2 = y.lst[ct];
		cs++;
		ct++;
		if
		:: x.lst[cs-1] != y.lst[ct-1] ->
			if
			:: c1 < c2 -> ret = -1;
			:: else -> ret = 1;
			fi;
			retd = true;
		:: x.lst[cs-1] != y.lst[ct-1] && c1 == 0 ->
			breaked = true;
		:: else ->
			count--;
		fi;
	:: else -> break;
	od;
	if
	:: retd -> skip;
	:: !retd -> ret = 0;
	fi;
	abstract_strncmp_end!ret;
}

init {
	listoption x, y;
	int ret;

	x.lst[0] = 2;
	x.lst[1] = 2;
	x.lst[2] = 0;

	y.lst[0] = 2;
	y.lst[1] = 1;
	y.lst[2] = 0;

	x.length = 4;
	y.length = 4;

	run abstract_strncmp(3);
	abstract_strncmp_start!x,y;
	abstract_strncmp_end?ret;

	assert (ret != 0);
}

