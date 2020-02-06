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

typedef intptr {
    int ptr;
    listoption data;    
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
chan sslBuffer_AppendVariable_new = [1] of {sslbuffer};
 
chan ssl_Encode_old = [1] of {sslbuffer};
chan ssl_Encode_new = [1] of {sslbuffer};

chan sslBuffer_AppendVariable_ret = [1] of {int};
chan sslBuffer_Append_Convert = [1] of {intConvert};

chan sslBuffer_AppendVariable_done = [1] of {bool};

chan sslBuffer_PORT_Memcpy_Num_buf_old_fst = [1] of {sslbuffer};
chan asslBuffer_PORT_Memcpy_Num_buf_old_snd = [1] of {intConvert};

chan sslBuffer_PORT_Memcpy_intptr_buf_old_fst = [1] of {sslbuffer};
chan asslBuffer_PORT_Memcpy_intptr_buf_old_snd = [1] of {intptr};

chan sslBuffer_PORT_Memcpy_intptr_buf_new = [1] of {sslbuffer};

chan sslBuffer_PORT_Memcpy_Num_buf_new = [1] of {sslbuffer};

chan dereference_UInt_res = [1] of {intptr};

proctype PORT_Memcpy_Num(int size) {
	sslbuffer buf1;
	intConvert value;
	int start, end;

	sslBuffer_PORT_Memcpy_Num_buf_old_fst ? buf1;
	asslBuffer_PORT_Memcpy_Num_buf_old_snd ? value;

	start = ((buf1.len0 < MAX_LENGTH) -> (buf1.len0 < 0 -> 0 : buf1.len0) : (MAX_LENGTH));
	end = ((size + buf1.len0) > (MAX_LENGTH) -> (MAX_LENGTH) : ((size + buf1.len0 < 0) -> 0 : size + buf1.len0));

	buf1.buf.initialized = Initialized;

	for(i,start,end-1)
		buf1.buf.lst[i] = value.a[i-(start)];
	rof(i);	

//	buf1.len0 = ((buf1.len0 == 0) && (size == 0) -> 0 : end);
	buf1.buf.length = ((buf1.len0 == 0) && (size == 0) -> 0 : end);

	
	sslBuffer_PORT_Memcpy_Num_buf_new ! buf1;
}

proctype PORT_Memcpy_intptr(int size) {
	sslbuffer buf1;
	intptr value;
	int start, end;

	sslBuffer_PORT_Memcpy_intptr_buf_old_fst ? buf1;
	asslBuffer_PORT_Memcpy_intptr_buf_old_snd ? value;

	start = ((buf1.len0 < MAX_LENGTH) -> (buf1.len0 < 0 -> 0 : buf1.len0) : (MAX_LENGTH));
	end = ((size + buf1.len0) > (MAX_LENGTH) -> (MAX_LENGTH) : ((size + buf1.len0 < 0) -> 0 : size + buf1.len0));

	buf1.buf.initialized = Initialized;

	printf("buf1.len0 = %d\n", buf1.len0);
	printf("size = %d\n", size);
	printf("start = %d\n", start);
	printf("end = %d\n", end);
	for(i,start,end-1)
		buf1.buf.lst[i] = value.data.lst[i-(start)];
	rof(i);	

//	buf1.len0 = ((buf1.len0 == 0) && (size == 0) -> 0 : end);
	buf1.buf.length = ((buf1.len0 == 0) && (size == 0) -> 0 : end);

		
	sslBuffer_PORT_Memcpy_intptr_buf_new ! buf1;
}

proctype convert(int value) {
	intConvert val_arr;
	byte temp[4];
	int tempval = value;
	for(i,0,3)
		temp[i] = tempval << 8*i;
		val_arr.a[i] = temp[i] >> 8*3;
	rof(i);
	sslBuffer_Append_Convert ! val_arr;
}

proctype ssl_EncodeUintX(int value; int size) {
	sslbuffer to;
	sslbuffer new;
	intConvert V;

	ssl_Encode_old?to;
	run convert(value);
	sslBuffer_Append_Convert?V;

	sslBuffer_PORT_Memcpy_Num_buf_old_fst ! to;
	asslBuffer_PORT_Memcpy_Num_buf_old_snd!V;

	run PORT_Memcpy_Num(size);
	sslBuffer_PORT_Memcpy_Num_buf_new ? new;

	ssl_Encode_new!new;


}

proctype dereference_UInt(int ptr; int length){
	intptr random;
	int start;
	int end;
	
	random.ptr = ptr;	

	do
	:: random.data.initialized = Initialized; break;
	:: random.data.initialized = Uninitialized; break;
	od;

	if
	:: random.data.initialized == Initialized ->
		end = ((length > MAX_LENGTH) -> MAX_LENGTH : length);
		random.data.length = end;
		for(i,0,end)
			do
			::random.data.lst[i] = random.data.lst[i] + 1;
			::break;
			od;
		rof(i);
	:: else -> skip;
	fi;

	dereference_UInt_res!random;

}

proctype sslBuffer_AppendVariable(int ptr; int length; int size) {
	int ret;

	int gret;
	bool gdone;

	sslbuffer buf1;
	sslBuffer_Append_buf1_old ? buf1;

	intptr snd_data;
	int copylen = length;
	int copysize = size;
	int shifted_csize;

	printf("size = %d\n", size);
	printf("length = %d\n", length);
	

	shifted_csize = copysize << 3;
	printf("shifted_csize = %d\n", shifted_csize);

	int shifted_clen = copylen;
	for(i,0,shifted_csize-1)
		shifted_clen = shifted_clen / 2;
	rof(i);
	printf("shifted_clen = %d\n", shifted_clen);


	if 
	:: ((size > 4) || (size < 1) || (shifted_clen != 0)) ->
		ret = -1;
		sslBuffer_AppendVariable_ret!ret;
	:: else ->
		sslBuffer_Grow_buf!buf1;
		run sslBuffer_Grow(buf1.len0 + length+ size);
		sslBuffer_Grow_ret?gret
		sslBuffer_Grow_done?gdone;
		gdone == true;
		sslBuffer_Grow_buf?buf1;
	
		if
		:: gret != 0 ->
			ret = -1;
			sslBuffer_AppendVariable_ret!ret;

		:: gret == 0 ->
			ssl_Encode_old!buf1;
			run ssl_EncodeUintX(length, size);
			ssl_Encode_new?buf1;

			buf1.len0 = buf1.len0 + size;

			run dereference_UInt(ptr, length);
			dereference_UInt_res?snd_data;

			if
			:: snd_data.data.initialized == Initialized ->
//				if
//				:: length != 0 ->
					sslBuffer_PORT_Memcpy_intptr_buf_old_fst ! buf1;
					asslBuffer_PORT_Memcpy_intptr_buf_old_snd ! snd_data;
		
					run PORT_Memcpy_intptr(length);
					sslBuffer_PORT_Memcpy_intptr_buf_new ? buf1;
				

//				:: else -> skip;
//				fi;
				buf1.len0 = buf1.len0 + length;
				ret = 0;
				sslBuffer_AppendVariable_ret!ret;
			:: else ->
				ret = -1;
				sslBuffer_AppendVariable_ret!ret;
			fi;				
		
		fi;
	fi;
	sslBuffer_AppendVariable_new!buf1;
	sslBuffer_AppendVariable_done!true;
		
}

init {
	int retval;
	sslbuffer init_buf1;

	int size;
	int length;
	bool done;
	bool cond_true;

	int len0;
	int len1;
	int final_len;
	int ptr;

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
	
	length = 1;
	do
	::  length < 16 -> length = length + 1;
	::  break;
	od;


/*	if
	:: length = 5;
	:: length = 6;
	:: length = 7;
	:: length = 8;
	:: length = 9;
	fi;
*/



	size = 1;
	do
	::  size < 4 -> size = size + 1;
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

	run sslBuffer_AppendVariable(ptr, length, size);
	sslBuffer_AppendVariable_done?done;

//	done == true;
	sslBuffer_AppendVariable_new?init_buf1;

	sslBuffer_AppendVariable_ret?retval;


	printf("retval = %d", retval);
	assert ((retval == 0) || (retval == -1));
	//assert ((retval == -1));
	//final_len = ((len0 + len1 > MAX_LENGTH) -> (MAX_LENGTH) : (len0 + len1));
	//cond_true = (init_buf1.len0 == final_len);
	final_len = ((len0 + size > MAX_LENGTH) -> MAX_LENGTH : len0 + size );

	if
	:: retval == 0 ->
		assert (init_buf1.buf.initialized == Initialized);
//		assert(init_buf1.len0 <= MAX_LENGTH)
//		assert(init_buf1.len0 == final_len)
	:: else -> skip;
	fi;

	

}

