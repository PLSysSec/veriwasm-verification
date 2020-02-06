/*
	To run:
		spin -search SSLBuffer_Clear.pml
	To examine violations:
		spin -t -p -s -r -c SSLBuffer_Clear.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "8 word list option" */
#define MAX_LENGTH 5

mtype = {Initialized, Uninitialized};

typedef listoption {
    mtype initialized;
    int lst;
 //   byte lst[MAX_LENGTH];
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

chan sslBuffer_grow_ret = [1] of {int};

chan sslBuffer_Skip_buf = [1] of {sslbuffer};
chan sslBuffer_Skip_offset = [1] of {savedOffset}; 
 
chan sslBuffer_skip_ret = [1] of {int};

chan sslBuffer_Skip_done = [1] of {bool};


/* just a stub */
proctype sslBuffer_grow() {
	int ret;
	do 
	:: ret = 0; sslBuffer_grow_ret!ret; break;
	:: ret = -1; sslBuffer_grow_ret!ret; break;
	od;
}


proctype sslBuffer_Skip(int size) {
	int ret;
	int gret;
	sslbuffer buf;
	savedOffset offset;

		run sslBuffer_grow();
		sslBuffer_grow_ret?gret
		sslBuffer_Skip_buf?buf;
		sslBuffer_Skip_offset?offset;	
	
		if
		:: gret != 0 ->
			ret = -1;

			sslBuffer_skip_ret!-1;
		:: gret == 0 ->
			if
			:: offset.initialized ==  Initialized->
				offset.length = buf.len0;
			:: else ->
				offset.length = 0;
			fi;
//			sslBuffer_Skip_offset!offset;
							
			buf.len0 = buf.len0 + size;
//			sslBuffer_Skip_buf!buf;
			
			ret = 0;
			sslBuffer_skip_ret!0;
		
		fi;
		sslBuffer_Skip_offset!offset;
		sslBuffer_Skip_buf!buf;
		sslBuffer_Skip_done!true;
		
}

init {
	int retval;
	sslbuffer init_buf;
	int size;
	bool done;
	savedOffset offset;


	do 
	:: offset.initialized = Initialized; break;
	:: offset.initialized = Uninitialized; break;
	od;

	init_buf.len0 = 1;

	sslBuffer_Skip_buf!init_buf;
	sslBuffer_Skip_offset!offset;


	run sslBuffer_Skip(size);
	sslBuffer_Skip_done?done;

//	done == true;
	sslBuffer_Skip_buf?init_buf;
	sslBuffer_Skip_offset?offset;	

	sslBuffer_skip_ret?retval;


	printf("retval = %d", retval);
	assert ((retval == 0) || (retval == -1));
	if
	:: retval == 0 ->
		if
		::offset.initialized == Initialized ->
			assert(offset.length == 1);
		:: else ->
			assert(offset.length == 0);
		fi;
		assert(init_buf.len0 == 1 + size);	
	:: else -> skip;
	fi;

	

}

