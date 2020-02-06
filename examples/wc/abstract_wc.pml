/*
	To run:
		spin -search -DVECTORSZ=1200 file.pml
	To examine violations:
		spin -t -p -s -r -c file.pml

	There should be no assertion violations and no invalid end states.
*/


typedef file {
    bool initialized;
};

/* Functions calls are modelled by sending messages starting and ending a function body.
*/

chan feof_start	= [1] of {file};
chan feof_end  	= [1] of {bool};

chan getc_start	= [1] of {bool};
chan getc_end  	= [1] of {byte};

chan isword_start	= [1] of {byte};
chan isword_end  	= [1] of {bool};

chan fopen_start	= [1] of {bool};
chan fopen_end  	= [1] of {file};

chan fclose_start	= [1] of {bool};
chan fclose_end  	= [1] of {bool};

chan perrf_start	= [1] of {bool};
chan perrf_end  	= [1] of {bool};

chan report_start	= [1] of {bool};
chan report_end  	= [1] of {bool};

chan getword_start	= [1] of {file};
chan getword_end  	= [1] of {bool};

chan counter_start	= [1] of {bool};
chan counter_end  	= [1] of {bool};

/* feof
	Returns -- nondeterministically -- true or false.
*/
proctype feof() {
	file f;
	bool ret;
	feof_start?f;
	if
	:: ret = true;
	:: ret = false;
	fi;
	feof_end!ret;
}

/* getc
	Returns -- nondeterministically -- a character.
*/
proctype getc() {
  bool b;
	byte ret = 0;
	getc_start?b;
	do
	:: ret = -1 ; break;
	:: ret < 255  -> ret++;
	:: break;
	od;
	getc_end!ret;
}


/* isword 
	Returns -- nondeterministically -- true or false.
*/
proctype isword() {
	byte c;
	bool ret;
	isword_start?c;
	if
	:: ret = true;
	:: ret = false;
	fi;
	isword_end!ret;
}


/* fopen
	Sets initialized to true or false.
*/
proctype fopen() {
	file f;
	bool b;
	fopen_start?b;
	if
	:: f.initialized = true;
	:: f.initialized = false;
	fi;
	fopen_end!f;
}


/* fclose
*/
proctype fclose() {
	bool b;
	fclose_start?b;
	fclose_end!b;
}

/* perff 
*/
proctype perrf() {
	bool b;
	perrf_start?b;
	perrf_end!b;
}



/* report
*/
proctype report() {
	bool b;
	report_start?b;
	report_end!b;
}




/* global variables */
int lcount, wcount, ccount;
int total_lcount, total_wcount, total_ccount;

/* getword */
proctype getword() {
	file f;
	bool feof_ret, isword_ret, ret, breaked, breaked1;
	byte c;

	getword_start?f;

	run feof();
	feof_start!f;
	feof_end?feof_ret;
	if
	:: feof_ret ->
		ret = false;
	:: !feof_ret ->
		run getc();
		getc_start!true;
		getc_end?c;
		do
		:: !breaked && c!= -1 ->
			run isword();
			isword_start!f;
			isword_end?isword_ret;
			if
			:: !isword_ret -> 
				ccount++;
				if
				:: c == 10 -> lcount++;
				:: else -> skip;
				fi;
				run getc();
				getc_start!true;
				getc_end?c;
			:: else ->
				breaked = true;
				wcount++;
			fi;
		:: else -> break;
		od;
		breaked = true;
		do
		:: !breaked1 && c != -1 ->
			ccount++;
			if
			:: c == 10 -> lcount++;
			:: else -> skip;
			fi;
			run isword();
			isword_start!f;
			isword_end?isword_ret;
			breaked1 = (isword_ret == 0);
			if
			:: !breaked1 ->
				run getc();
				getc_start!true;
				getc_end?c;
			:: else -> skip;
			fi;
		:: else -> break;
		od;
		breaked1 = true;
		ret = (c != -1);
	fi;
	getword_end!ret;
}

/* counter */
proctype counter () {
	file f;
	byte c;
	bool b, ret;

	counter_start?b;

	run fopen();
	fopen_start!b;
	fopen_end?f;
	if
	:: !f.initialized ->
		run perrf();
		perrf_start!b;
		perrf_end?b;
	:: else -> skip
	fi;
	wcount = 0;
	ccount = 0;
	lcount = 0;
	
	run getword();
	getword_start!f;
	getword_end?ret;
	do
	:: ret ->
		run getword();
		getword_start!f;
		getword_end?ret;
	:: else -> break;
	od;
	
	run fclose();
	fclose_start!b;
	fclose_end?b;

	run report();
	report_start!b;
	report_end?b;

	total_wcount = total_wcount + wcount;
	total_lcount = total_lcount + lcount;
	total_ccount = total_ccount + ccount;
	
	counter_end!b;
}


init {
	bool b;
	run counter();
	counter_start!b;
	counter_end?b;
}

