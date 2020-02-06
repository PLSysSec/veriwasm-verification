/*
	To run:
		spin -search SSLBuffer_Clear.pml
	To examine violations:
		spin -t -p -s -r -c SSLBuffer_Clear.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "8 word list option" */
#define MAX_LENGTH 20
#define for(I,low,high) \
	byte I; \
	I = low ; \
	do \
	:: ( I > high ) -> break \
	:: else ->
		#define rof(I) \
		; I++ \
	od




mtype = {Initialized, Uninitialized};

typedef listoption {
    mtype initialized;
    int length;
   byte lst[MAX_LENGTH];
};

/* Modelling the sslbuffer */
typedef sslbuffer {
	int len0; /* len is reserved keyword */
	int space;
	bool fixed;
	listoption buf;
};

typedef savedOffset{
	mtype initialized;
	int length;
};

/* Functions calls are modelled by sending messages starting and ending a function body.

sslbuffer buf;
*/

chan sslBuffer_Grow_ret = [1] of {int};

chan sslBuffer_Grow_buf = [1] of {sslbuffer};


chan sslBuffer_Grow_done = [1] of {bool};


chan PORT_Realloc_new = [1] of {listoption};
chan PORT_Realloc_old = [1] of {listoption};

chan PORT_Alloc_new = [1] of {listoption};


/* just a stub 
proctype sslBuffer_grow() {
	int ret;
	do 
	:: ret = 0; sslBuffer_grow_ret!ret; break;
	:: ret = -1; sslBuffer_grow_ret!ret; break;
	od;
}
*/

proctype PORT_Realloc(int newLen){
	listoption new, x;
	int size;

	size = ((newLen -1) > (MAX_LENGTH - 1) -> (MAX_LENGTH - 1) : (newLen -1));
	PORT_Realloc_old ? x;
	
	new .initialized = Initialized;
	new.length = size;
	for(i, 0, size)
		new.lst[i] = x.lst[i];
	rof(i);
	PORT_Realloc_new!new;
}

proctype Alloc(int newLen){
	listoption new;
	new .initialized = Initialized;
	new.length = newLen;
	PORT_Alloc_new!new;
}



proctype sslBuffer_Grow(int newLen) {
	int ret;
	sslbuffer buf;

	sslBuffer_Grow_buf?buf;
	if
	:: buf.fixed ->
 
		if
		:: newLen > buf.space ->
			ret = -1;
		:: else ->
			ret = 0;
		fi;
		sslBuffer_Grow_buf!buf;
	:: else ->
		newLen = ((newLen > (buf.len0 + 1024)) -> newLen : (buf.len0 + 1024));
		if
		:: newLen > buf.space ->
			if
			:: buf.buf.initialized == Initialized ->
				run PORT_Realloc(newLen);
				PORT_Realloc_old ! buf.buf;
				PORT_Realloc_new?buf.buf;
			:: else ->
				run Alloc(newLen);
				PORT_Alloc_new?buf.buf;
			fi;
			buf.space = newLen;
			ret  = 0;
			sslBuffer_Grow_buf!buf;
		:: else ->
			ret = -1;
		fi;
	
	fi;

	sslBuffer_Grow_ret!ret ;
	sslBuffer_Grow_done!true;
		
}

init {
	int retval;
	sslbuffer init_buf;
	int newLen;
	bool init_init;
	bool init_fixed; 

	bool done;

	do 
	:: init_buf.fixed = true; init_fixed = true; break;
	:: init_buf.fixed = false; init_fixed = false; break;
	od;


	do 
	:: init_buf.buf.initialized = Initialized; init_init = true; break;
	:: init_buf.buf.initialized = Uninitialized; init_init = false; break;
	od;



	sslBuffer_Grow_buf!init_buf;

	run sslBuffer_Grow(newLen);
	sslBuffer_Grow_done?done;

	done == true;

	sslBuffer_Grow_buf?init_buf;
	sslBuffer_Grow_ret?retval;


	printf("retval = %d", retval);


	assert ((retval == 0) || (retval == -1));


	if
	:: retval == 0 ->
		if
		::!init_init && !init_fixed ->
			assert(init_buf.buf.initialized == Initialized);
		:: init_init ->
			assert(init_buf.buf.initialized == Initialized);
		:: else ->
			skip;
		fi;
	:: else -> skip;
	fi;

	

}

