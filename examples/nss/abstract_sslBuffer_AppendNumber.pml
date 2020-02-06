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

//----------------------SSLBuffer_Grow-----------------------

chan sslBuffer_Grow_ret = [1] of {int};

chan sslBuffer_Grow_buf = [1] of {sslbuffer};


chan sslBuffer_Grow_done = [1] of {bool};


chan PORT_Realloc_new = [1] of {listoption};
chan PORT_Realloc_old = [1] of {listoption};

chan PORT_Alloc_new = [1] of {listoption};

proctype PORT_Realloc(int newLen){
	listoption new, x;
	int size;

	size = ((newLen) > (MAX_LENGTH) -> (MAX_LENGTH) : (newLen));
	PORT_Realloc_old ? x;
	
	new .initialized = Initialized;
	new.length = size;
	for(i, 0, size-1)
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

//------------------------------------------------------

typedef intConvert{
	byte a[4];
};


chan sslBuffer_Append_buf1_old = [1] of {sslbuffer};
chan sslBuffer_Append_buf_new = [1] of {sslbuffer};
 
chan ssl_Encode_old = [1] of {sslbuffer};
chan ssl_Encode_new = [1] of {sslbuffer};

chan sslBuffer_Append_ret = [1] of {int};
chan sslBuffer_Append_Convert = [1] of {intConvert};

chan sslBuffer_Append_done = [1] of {bool};

chan sslBuffer_PORT_Memcpy_buf_old_fst = [1] of {sslbuffer};
chan asslBuffer_PORT_Memcpy_buf_old_snd = [1] of {intConvert};

chan sslBuffer_PORT_Memcpy_buf_new = [1] of {sslbuffer};


proctype PORT_Memcpy(int size) {
	sslbuffer buf1;
	intConvert value;
	int start, end;

	sslBuffer_PORT_Memcpy_buf_old_fst ? buf1;
	asslBuffer_PORT_Memcpy_buf_old_snd ? value;

	start = ((buf1.len0 < MAX_LENGTH) -> (buf1.len0 < 0 -> 0 : buf1.len0) : (MAX_LENGTH));
	end = ((size + buf1.len0) > (MAX_LENGTH) -> (MAX_LENGTH) : ((size + buf1.len0 < 0) -> 0 : size + buf1.len0));

	buf1.buf.initialized = Initialized;

	for(i,start,end-1)
		buf1.buf.lst[i] = value.a[i-(start)];
	rof(i);	

	buf1.len0 = ((buf1.len0 == 0) && (size == 0) -> 0 : end);
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
	sslBuffer_Append_Convert ! val_arr;
}

proctype ssl_EncodeUintX(int value; int size) {
	sslbuffer to;
	sslbuffer new;
	intConvert V;

	run convert(value);
	sslBuffer_Append_Convert?V;

	ssl_Encode_old?to;

	sslBuffer_PORT_Memcpy_buf_old_fst ! to;
	asslBuffer_PORT_Memcpy_buf_old_snd!V;

	run PORT_Memcpy(size);
	sslBuffer_PORT_Memcpy_buf_new ? new;

	ssl_Encode_new!new;


}

proctype sslBuffer_AppendNumber(int value; int size) {
	int ret;
	int gret;
	bool gdone;

	sslbuffer buf1, buf2;
	sslBuffer_Append_buf1_old ? buf1;

	sslBuffer_Grow_buf!buf1;
	run sslBuffer_Grow(buf1.len0 + size);
	sslBuffer_Grow_ret?gret
	sslBuffer_Grow_done?gdone;
	gdone == true;
	sslBuffer_Grow_buf?buf1;
	
		if
		:: gret != 0 ->
			ret = -1;
			sslBuffer_Append_ret!ret;

		:: gret == 0 ->
/*			run convert(value);
			sslBuffer_Append_Convert?V;
			sslBuffer_PORT_Memcpy_buf_old_fst ! buf1;
			asslBuffer_PORT_Memcpy_buf_old_snd!V;
			run PORT_Memcpy(size);
			sslBuffer_PORT_Memcpy_buf_new ? buf1;
*/
			
			ssl_Encode_old!buf1;
			run ssl_EncodeUintX(value, size);
			ssl_Encode_new?buf1;
			ret = 0;
			sslBuffer_Append_ret!ret;
		
		fi;
		sslBuffer_Append_buf_new!buf1;
		sslBuffer_Append_done!true;
		
}

init {
	int retval;
	sslbuffer init_buf1;

	int size;
	int value;
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
	::  init_buf1.len0 < 8 -> init_buf1.len0 = init_buf1.len0 + 1;
	::  break;
	od;


	size = 0;
	do
	::  size < 4 -> size++;
	::  break;
	od;

	init_buf1.space = 0;
	
	do
	::  init_buf1.space <= 8 -> init_buf1.space++;
	::  break;
	od;



	sslBuffer_Append_buf1_old!init_buf1;

	len0 = init_buf1.len0;
	size = 4;

	run sslBuffer_AppendNumber(value, size);
	sslBuffer_Append_done?done;

//	done == true;
	sslBuffer_Append_buf_new?init_buf1;

	sslBuffer_Append_ret?retval;


	printf("retval = %d", retval);
	assert ((retval == 0) || (retval == -1));
	//assert ((retval == -1));
	//final_len = ((len0 + len1 > MAX_LENGTH) -> (MAX_LENGTH) : (len0 + len1));
	//cond_true = (init_buf1.len0 == final_len);
	final_len = ((len0 + size > MAX_LENGTH) -> MAX_LENGTH : len0 + size );

	if
	:: retval == 0 ->
		assert (init_buf1.buf.initialized == Initialized);
		assert(init_buf1.len0 <= MAX_LENGTH)
		assert(init_buf1.len0 == final_len)
	:: else -> skip;
	fi;
*/
	

}

