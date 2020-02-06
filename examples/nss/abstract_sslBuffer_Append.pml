/*
	To run:
		spin -search SSLBuffer_Clear.pml
	To examine violations:
		spin -t -p -s -r -c SSLBuffer_Clear.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "8 word list option" */
#define MAX_LENGTH 5
#define for(I,low,high) \
	int I; \
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
/* Functions calls are modelled by sending messages starting and ending a function body.

sslbuffer buf;
*/

chan sslBuffer_grow_ret = [1] of {int};

chan sslBuffer_Append_buf1_old = [1] of {sslbuffer};
chan sslBuffer_Append_buf2_old = [1] of {sslbuffer};
chan sslBuffer_Append_buf_new = [1] of {sslbuffer};
 
chan sslBuffer_Append_ret = [1] of {int};

chan sslBuffer_Append_done = [1] of {bool};

chan sslBuffer_PORT_Memcpy_buf_old_fst = [1] of {sslbuffer};
chan sslBuffer_PORT_Memcpy_buf_old_snd = [1] of {sslbuffer};

chan sslBuffer_PORT_Memcpy_buf_new = [1] of {sslbuffer};


/* just a stub */
proctype sslBuffer_grow() {
	int ret;
	do 
	:: ret = 0; sslBuffer_grow_ret!ret; break;
	:: ret = -1; sslBuffer_grow_ret!ret; break;
	od;
}

proctype PORT_Memcpy(int newLen) {
	sslbuffer buf1;
	sslbuffer buf2;
	int start, end;

	sslBuffer_PORT_Memcpy_buf_old_fst ? buf1;
	sslBuffer_PORT_Memcpy_buf_old_snd ? buf2;
	
//	start = ((buf1.buf.length -1) > (MAX_LENGTH - 1) -> (MAX_LENGTH - 1) : ((buf1.buf.length < 1) -> 0 : buf1.buf.length -1));
	start = ((buf1.len0 < MAX_LENGTH) -> (buf1.len0) : (MAX_LENGTH));
	end = ((newLen + buf1.len0 -1) > (MAX_LENGTH - 1) -> (MAX_LENGTH - 1) : ((newLen + buf1.len0 < 1) -> 0 : newLen + buf1.len0 -1));

	buf1.buf.initialized = Initialized;

	for(i,start,end)
		buf1.buf.lst[i] = buf2.buf.lst[i];
	rof(i);	

	buf1.len0 = ((buf1.len0 == 0) && (newLen == 0) -> 0 : end + 1);
	buf1.buf.length = ((buf1.len0 == 0) && (newLen == 0) -> 0 : end + 1);
	
	sslBuffer_PORT_Memcpy_buf_new ! buf1;
}



proctype sslBuffer_Append(int size) {
	int ret;
	int gret;
	sslbuffer buf1, buf2;

		run sslBuffer_grow();
		sslBuffer_grow_ret?gret

		sslBuffer_Append_buf1_old ? buf1;
		sslBuffer_Append_buf2_old ? buf2;
	
		if
		:: gret != 0 ->
			ret = -1;
			sslBuffer_Append_ret!ret;

		:: gret == 0 ->
			sslBuffer_PORT_Memcpy_buf_old_fst ! buf1;
			sslBuffer_PORT_Memcpy_buf_old_snd ! buf2;
			run PORT_Memcpy(size);
			sslBuffer_PORT_Memcpy_buf_new ? buf1;
			ret = 0;
			sslBuffer_Append_ret!ret;
		
		fi;
		sslBuffer_Append_buf_new!buf1;
		sslBuffer_Append_done!true;
		
}

init {
	int retval;
	sslbuffer init_buf1;
	sslbuffer init_buf2;

	int size;
	bool done;
	bool cond_true;

	int len0;
	int len1;
	int final_len;


	do 
	:: init_buf1.buf.initialized = Initialized; break;
	:: init_buf1.buf.initialized = Uninitialized; break;
	od;

	do 
	:: init_buf2.buf.initialized = Initialized; break;
	:: init_buf2.buf.initialized = Uninitialized; break;
	od;



	init_buf2.len0 = 0;
	do
	:: init_buf2.len0 < 7 -> init_buf2.len0++;
	:: break;
	od;


	init_buf1.len0 = 0;
	do
	:: init_buf1.len0 < 7 -> init_buf1.len0++;
	:: break;
	od;

	sslBuffer_Append_buf1_old!init_buf1;
	sslBuffer_Append_buf2_old!init_buf2;

	len0 = init_buf1.len0;
	len1 = init_buf2.len0;

	run sslBuffer_Append(init_buf2.len0);
	sslBuffer_Append_done?done;

//	done == true;
	sslBuffer_Append_buf_new?init_buf1;

	sslBuffer_Append_ret?retval;


	printf("retval = %d", retval);
	assert ((retval == 0) || (retval == -1));
	final_len = ((len0 + len1 > MAX_LENGTH) -> (MAX_LENGTH) : (len0 + len1));
	cond_true = (init_buf1.len0 == final_len);


	if
	:: retval == 0 ->
		assert (init_buf1.buf.initialized == Initialized);
		assert(init_buf1.len0 <= MAX_LENGTH)
		assert(((len0 + len1 > MAX_LENGTH)  -> (init_buf1.len0 == MAX_LENGTH) : true));
		assert ((init_buf1.len0 == final_len));
	:: else -> skip;
	fi;

	

}

