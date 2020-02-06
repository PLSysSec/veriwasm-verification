/*
	To run:
		spin -search SSLBuffer_Clear.pml
	To examine violations:
		spin -t -p -s -r -c SSLBuffer_Clear.pml

	There should be no assertion violations and no invalid end states.
*/


/* Modelling the Isabelle type "8 word list option" */
#define MAX_LENGTH 10
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

//------------------------------------------------------

typedef intConvert{
	byte a[4];
};


chan sslBuffer_InsertLen_buf1_old = [1] of {sslbuffer};
chan sslBuffer_InsertLen_buf_new = [1] of {sslbuffer};
 
chan ssl_Encode_old = [1] of {sslbuffer};
chan ssl_Encode_new = [1] of {sslbuffer};

chan sslBuffer_InsertLen_ret = [1] of {int};
chan sslBuffer_InsertLen_Convert = [1] of {intConvert};

chan sslBuffer_InsertLen_done = [1] of {bool};

chan sslBuffer_PORT_Memcpy_buf_old_fst = [1] of {sslbuffer};
chan asslBuffer_PORT_Memcpy_buf_old_snd = [1] of {intConvert};

chan sslBuffer_PORT_Memcpy_buf_new = [1] of {sslbuffer};


proctype PORT_Memcpy(int at; int size) {
	sslbuffer buf1;
	intConvert value;
	int start, end;

	sslBuffer_PORT_Memcpy_buf_old_fst ? buf1;
	asslBuffer_PORT_Memcpy_buf_old_snd ? value;

	start = ((at < MAX_LENGTH) -> (at < 0 -> 0 : at) : (MAX_LENGTH));
	end = ((size + at) > (MAX_LENGTH) -> (MAX_LENGTH) : ((size + at < 0) -> 0 : size + at));

	buf1.buf.initialized = Initialized;

	for(i,start,end-1)
		buf1.buf.lst[i] = value.a[i-(start)];
	rof(i);	

//	buf1.len0 = ((buf1.len0 == 0) && (size == 0) -> 0 : end);
	buf1.buf.length = ((buf1.len0 == 0) && (size == 0) -> 0 : end);

	
	sslBuffer_PORT_Memcpy_buf_new ! buf1;
}

proctype convert(int value) {
	intConvert val_arr;
	byte temp[4];
	for(i,0,3)
		temp[i] = value << 8*i;
		val_arr.a[i] = temp[i] >> 8*3;
	rof(i);
	sslBuffer_InsertLen_Convert ! val_arr;
}

proctype ssl_EncodeUintX(int at; int value; int size) {
	sslbuffer to;
	sslbuffer new;
	intConvert V;

	ssl_Encode_old?to;

	run convert(value);
	sslBuffer_InsertLen_Convert?V;

	sslBuffer_PORT_Memcpy_buf_old_fst ! to;
	asslBuffer_PORT_Memcpy_buf_old_snd!V;

	run PORT_Memcpy(at, size);
	sslBuffer_PORT_Memcpy_buf_new ? new;

	ssl_Encode_new!new;


}

proctype sslBuffer_InsertLength(int at; int size) {
	int ret;
	int gret;
	bool gdone;

	int length;

	sslbuffer buf1;
	sslBuffer_InsertLen_buf1_old ? buf1;

	length = buf1.len0 - (at + size);
	if
	:: length >= 0 ->
		int lencpy = length;
		int sizecpy = size;
	
		int shiftedsize = sizecpy << 3;
		int shiftedlen = lencpy >> shiftedsize;
	
		if
		:: ((size > 4) || (size < 1) || (shiftedlen != 0)) ->
			ret = -1;
			sslBuffer_InsertLen_ret!ret;
	
		:: else ->
			ssl_Encode_old!buf1;
			run ssl_EncodeUintX(at, length, size);
			ssl_Encode_new?buf1;
			ret = 0;
			sslBuffer_InsertLen_ret!ret;
		
		fi;
	:: else ->
		ret = -1;
		sslBuffer_InsertLen_ret!ret;
	fi;
	sslBuffer_InsertLen_buf_new!buf1;
	sslBuffer_InsertLen_done!true;
	
}

init {
	int retval;
	sslbuffer init_buf1;

	int size;
	int at;
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
	:: init_buf1.fixed = true; break;
	:: init_buf1.fixed = false; break;
	od;
	

	init_buf1.len0 = 0;
	do
	::  init_buf1.len0 < 16 -> init_buf1.len0 = init_buf1.len0 + 1;
	::  break;
	od;


	size = 1;
	do
	::  size < 4 -> size++;
	::  break;
	od;

	at = 0;
	do
	::  at < 20 -> at++;
	::  break;
	od;

	init_buf1.space = 0;
	
	do
	::  init_buf1.space <= 8 -> init_buf1.space++;
	::  break;
	od;



	sslBuffer_InsertLen_buf1_old!init_buf1;

	len0 = init_buf1.len0;

	run sslBuffer_InsertLength(at, size);
	sslBuffer_InsertLen_done?done;

//	done == true;
	sslBuffer_InsertLen_buf_new?init_buf1;

	sslBuffer_InsertLen_ret?retval;
//	final_len = len0 - (at + size);
	final_len = (at + size);


	printf("retval = %d", retval);
	assert ((retval == 0) || (retval == -1));
	if
	:: retval == 0 ->
		assert (init_buf1.buf.initialized == Initialized);
//		assert(init_buf1.len0 <= MAX_LENGTH)
		assert(init_buf1.buf.length == (final_len > MAX_LENGTH -> MAX_LENGTH : final_len));
	:: else -> skip;
	fi;
*/
	

}

