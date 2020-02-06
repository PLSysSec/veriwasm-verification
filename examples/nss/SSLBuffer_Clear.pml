/*
	To run:
		spin -search SSLBuffer_Clear.pml
	To examine violations:
		spin -t -p -s -r -c SSLBuffer_Clear.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "8 word list option" */
#define MAX_LENGTH 5
typedef listoption {
    bool initialized;
    byte lst[MAX_LENGTH];
};

/* Modelling the sslbuffer */
typedef sslbuffer {
	int len0; /* len is reserved keyword */
	int space;
	bool fixed;
	listoption buf;
};


/* Functions calls are modelled by sending messages starting and ending a function body.
*/
chan sslBuffer_Clear_start = [1] of {sslbuffer};
chan sslBuffer_Clear_end = [1] of {sslbuffer};

chan PORT_Free_start = [1] of {bool};
chan PORT_Free_end = [1] of {bool};

/* just a stub */
active proctype PORT_Free() {
	bool b;
end:
	do :: PORT_Free_start?b ->
		PORT_Free_end!b
	od
}

active proctype sslBuffer_Clear() {
	/* receive the buffer as a parameter */
	sslbuffer buf;
	bool b;
end:
	do :: sslBuffer_Clear_start?buf ->
		if
		:: !buf.fixed ->
			if 
			:: buf.buf.initialized ->
				PORT_Free_start!true;
				PORT_Free_end?b;
				buf.buf.initialized = false;
			:: !buf.buf.initialized -> skip
			fi;
			buf.space = 0;
		:: buf.fixed -> skip
		fi;
		buf.len0 = 0;
		sslBuffer_Clear_end!buf;
	od;
}

init {
	sslbuffer buf;

	do
	:: buf.fixed = true; break;
	:: buf.fixed = false; break;
	od;
	do
	:: buf.buf.initialized = true; break;
	:: buf.buf.initialized = false; break;
	od;
	sslBuffer_Clear_start!buf;
	sslBuffer_Clear_end?buf;
	assert (buf.fixed || !buf.buf.initialized);
	assert (buf.len0 == 0);
}
