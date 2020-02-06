
functor LexMLYACC(structure Tokens : Mlyacc_TOKENS
		  structure Hdr : HEADER (* = Header *)
		    where type prec = Header.prec
		      and type inputSource = Header.inputSource) : ARG_LEXER
=
   struct
    type int = Int.int
    structure UserDeclarations =
      struct
(*
 * @TAG(OTHER_PRINCETON_OSS)
 *)
(* Modified by sweeks@acm.org on 2000-8-24.
 * Ported to MLton.
 *)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi

   yacc.lex: Lexer specification
 *)

structure Tokens = Tokens
type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

type lexarg = Hdr.inputSource
type arg = lexarg

open Tokens
val error = Hdr.error
val lineno = Hdr.lineno
val text = Hdr.text

val pcount: int ref = ref 0
val commentLevel: int ref = ref 0
val actionstart: int ref = ref 0

val eof = fn i => (if (!pcount)>0 then
			error i (!actionstart)
			      " eof encountered in action beginning here !"
		   else (); EOF(!lineno,!lineno))

val Add = fn s => (text := s::(!text))


local val dict = [("%prec",PREC_TAG),("%term",TERM),
	       ("%nonterm",NONTERM), ("%eop",PERCENT_EOP),("%start",START),
	       ("%prefer",PREFER),("%subst",SUBST),("%change",CHANGE),
	       ("%keyword",KEYWORD),("%name",NAME),
	       ("%verbose",VERBOSE), ("%nodefault",NODEFAULT),
	       ("%value",VALUE), ("%noshift",NOSHIFT),
	       ("%header",PERCENT_HEADER),("%pure",PERCENT_PURE),
	       ("%token_sig_info",PERCENT_TOKEN_SIG_INFO),
	       ("%arg",PERCENT_ARG),
	       ("%pos",PERCENT_POS)]
in val lookup =
     fn (s,left,right) =>
	 let fun f ((a,d)::b) = if a=s then d(left,right) else f b
	       | f nil = UNKNOWN(s,left,right)
	 in f dict
	 end
end

fun inc (ri as ref i : int ref) = (ri := i+1)
fun dec (ri as ref i : int ref) = (ri := i-1)

end (* end of user routines *)
exception LexError (* raised if illegal leaf action tried *)
structure Internal =
	struct

datatype yyfinstate = N of int
type statedata = {fin : yyfinstate list, trans: string}
(* transition & final state table *)
val tab = let
val s = [ 
 (0, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (1, 
"\015\015\015\015\015\015\015\015\015\015\021\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\019\015\015\017\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\015\
\\015"
),
 (3, 
"\022\022\022\022\022\022\022\022\022\065\067\022\022\022\022\022\
\\022\022\022\022\022\022\022\022\022\022\022\022\022\022\022\022\
\\065\022\022\022\022\045\022\043\041\022\040\022\039\037\022\022\
\\035\035\035\035\035\035\035\035\035\035\034\022\022\022\022\022\
\\022\026\026\026\026\026\026\026\026\026\026\026\026\026\026\026\
\\026\026\026\026\026\026\026\026\026\026\026\022\022\022\022\022\
\\022\026\026\026\026\026\031\026\026\026\026\026\026\026\026\029\
\\026\026\026\026\026\026\026\026\026\026\026\025\024\023\022\022\
\\022"
),
 (5, 
"\068\068\068\068\068\068\068\068\068\068\021\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\072\068\068\068\068\068\070\069\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068"
),
 (7, 
"\073\073\073\073\073\073\073\073\073\075\021\073\073\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\075\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\074\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\073\
\\073"
),
 (9, 
"\077\077\077\077\077\077\077\077\077\077\021\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\081\080\078\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077"
),
 (11, 
"\083\083\083\083\083\083\083\083\083\083\088\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\087\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\084\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083"
),
 (13, 
"\089\089\089\089\089\089\089\089\089\089\021\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\093\092\090\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089"
),
 (15, 
"\016\016\016\016\016\016\016\016\016\016\000\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016\016\016\016\016\000\016\016\000\016\016\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\016\
\\016"
),
 (17, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\018\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (19, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\020\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (26, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\027\000\000\000\000\000\000\028\000\
\\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\000\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\027\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\
\\000"
),
 (29, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\027\000\000\000\000\000\000\028\000\
\\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\000\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\027\
\\000\027\027\027\027\027\030\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\
\\000"
),
 (31, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\027\000\000\000\000\000\000\028\000\
\\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\000\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\027\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\032\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\
\\000"
),
 (32, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\027\000\000\000\000\000\000\028\000\
\\027\027\027\027\027\027\027\027\027\027\000\000\000\000\000\000\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\027\027\027\027\027\027\027\027\027\000\000\000\000\027\
\\000\027\027\027\027\027\027\027\027\027\027\027\027\027\027\027\
\\027\027\033\027\027\027\027\027\027\027\027\000\000\000\000\000\
\\000"
),
 (35, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\036\036\036\036\036\036\036\036\036\036\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (37, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\038\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (41, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\042\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (43, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\044\000\000\000\000\000\000\000\000\
\\044\044\044\044\044\044\044\044\044\044\000\000\000\000\000\000\
\\000\044\044\044\044\044\044\044\044\044\044\044\044\044\044\044\
\\044\044\044\044\044\044\044\044\044\044\044\000\000\000\000\044\
\\000\044\044\044\044\044\044\044\044\044\044\044\044\044\044\044\
\\044\044\044\044\044\044\044\044\044\044\044\000\000\000\000\000\
\\000"
),
 (45, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\064\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\060\046\052\046\
\\046\046\047\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (46, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (47, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\048\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (48, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\049\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (49, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\050\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (50, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\051\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (52, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\053\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (53, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\054\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (54, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\055\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (55, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\056\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (56, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\057\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (57, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\058\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (58, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\059\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (60, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\061\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (61, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\062\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\046\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (62, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\046\
\\000\046\046\046\046\046\046\046\046\046\046\046\046\046\046\046\
\\046\046\046\046\063\046\046\046\046\046\046\000\000\000\000\000\
\\000"
),
 (65, 
"\000\000\000\000\000\000\000\000\000\066\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\066\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (68, 
"\068\068\068\068\068\068\068\068\068\068\000\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\000\068\068\068\068\068\000\000\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\068\
\\068"
),
 (70, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\071\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (75, 
"\000\000\000\000\000\000\000\000\000\076\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\076\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (77, 
"\077\077\077\077\077\077\077\077\077\077\000\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\000\000\000\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\077\
\\077"
),
 (78, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\079\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (81, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\082\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (83, 
"\083\083\083\083\083\083\083\083\083\083\000\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\000\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\000\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\083\
\\083"
),
 (84, 
"\000\000\000\000\000\000\000\000\000\086\086\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\086\000\085\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (89, 
"\089\089\089\089\089\089\089\089\089\089\000\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\000\000\000\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\089\
\\089"
),
 (90, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\091\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
 (93, 
"\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\094\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\\000"
),
(0, "")]
fun f x = x 
val s = map f (rev (tl (rev s))) 
exception LexHackingError 
fun look ((j,x)::r, i) = if i = j then x else look(r, i) 
  | look ([], i) = raise LexHackingError
fun g {fin=x, trans=i} = {fin=x, trans=look(s,i)} 
in Vector.fromList(map g 
[{fin = [], trans = 0},
{fin = [], trans = 1},
{fin = [], trans = 1},
{fin = [], trans = 3},
{fin = [], trans = 3},
{fin = [], trans = 5},
{fin = [], trans = 5},
{fin = [], trans = 7},
{fin = [], trans = 7},
{fin = [], trans = 9},
{fin = [], trans = 9},
{fin = [], trans = 11},
{fin = [], trans = 11},
{fin = [], trans = 13},
{fin = [], trans = 13},
{fin = [(N 11),(N 18)], trans = 15},
{fin = [(N 11)], trans = 15},
{fin = [(N 18)], trans = 17},
{fin = [(N 2)], trans = 0},
{fin = [(N 18)], trans = 19},
{fin = [(N 14)], trans = 0},
{fin = [(N 16)], trans = 0},
{fin = [(N 94)], trans = 0},
{fin = [(N 36),(N 94)], trans = 0},
{fin = [(N 87),(N 94)], trans = 0},
{fin = [(N 34),(N 94)], trans = 0},
{fin = [(N 90),(N 94)], trans = 26},
{fin = [(N 90)], trans = 26},
{fin = [(N 77)], trans = 0},
{fin = [(N 90),(N 94)], trans = 29},
{fin = [(N 28),(N 90)], trans = 26},
{fin = [(N 90),(N 94)], trans = 31},
{fin = [(N 90)], trans = 32},
{fin = [(N 32),(N 90)], trans = 26},
{fin = [(N 85),(N 94)], trans = 0},
{fin = [(N 80),(N 94)], trans = 35},
{fin = [(N 80)], trans = 35},
{fin = [(N 94)], trans = 37},
{fin = [(N 43)], trans = 0},
{fin = [(N 38),(N 94)], trans = 0},
{fin = [(N 40),(N 94)], trans = 0},
{fin = [(N 92),(N 94)], trans = 41},
{fin = [(N 5)], trans = 0},
{fin = [(N 73),(N 94)], trans = 43},
{fin = [(N 73)], trans = 43},
{fin = [(N 94)], trans = 45},
{fin = [(N 70)], trans = 46},
{fin = [(N 70)], trans = 47},
{fin = [(N 70)], trans = 48},
{fin = [(N 70)], trans = 49},
{fin = [(N 70)], trans = 50},
{fin = [(N 56),(N 70)], trans = 46},
{fin = [(N 70)], trans = 52},
{fin = [(N 70)], trans = 53},
{fin = [(N 70)], trans = 54},
{fin = [(N 70)], trans = 55},
{fin = [(N 70)], trans = 56},
{fin = [(N 70)], trans = 57},
{fin = [(N 70)], trans = 58},
{fin = [(N 66),(N 70)], trans = 46},
{fin = [(N 70)], trans = 60},
{fin = [(N 70)], trans = 61},
{fin = [(N 70)], trans = 62},
{fin = [(N 49),(N 70)], trans = 46},
{fin = [(N 83)], trans = 0},
{fin = [(N 25),(N 94)], trans = 65},
{fin = [(N 25)], trans = 65},
{fin = [(N 20)], trans = 0},
{fin = [(N 103)], trans = 68},
{fin = [(N 98)], trans = 0},
{fin = [(N 96)], trans = 70},
{fin = [(N 8)], trans = 0},
{fin = [(N 100)], trans = 0},
{fin = [(N 147)], trans = 0},
{fin = [(N 145),(N 147)], trans = 0},
{fin = [(N 143),(N 147)], trans = 75},
{fin = [(N 143)], trans = 75},
{fin = [(N 114)], trans = 77},
{fin = [(N 105)], trans = 78},
{fin = [(N 108)], trans = 0},
{fin = [(N 105)], trans = 0},
{fin = [(N 105)], trans = 81},
{fin = [(N 111)], trans = 0},
{fin = [(N 134)], trans = 83},
{fin = [(N 129)], trans = 84},
{fin = [(N 137)], trans = 0},
{fin = [(N 140)], trans = 0},
{fin = [(N 127)], trans = 0},
{fin = [(N 131)], trans = 0},
{fin = [(N 125)], trans = 89},
{fin = [(N 116)], trans = 90},
{fin = [(N 119)], trans = 0},
{fin = [(N 116)], trans = 0},
{fin = [(N 116)], trans = 93},
{fin = [(N 122)], trans = 0}])
end
structure StartStates =
	struct
	datatype yystartstate = STARTSTATE of int

(* start state definitions *)

val A = STARTSTATE 3;
val CODE = STARTSTATE 5;
val COMMENT = STARTSTATE 9;
val EMPTYCOMMENT = STARTSTATE 13;
val F = STARTSTATE 7;
val INITIAL = STARTSTATE 1;
val STRING = STARTSTATE 11;

end
type result = UserDeclarations.lexresult
	exception LexerError (* raised if illegal leaf action tried *)
end

type int = Int.int
fun makeLexer (yyinput: int -> string) =
let	val yygone0:int=0
	val yyb = ref "\n" 		(* buffer *)
	val yybl: int ref = ref 1		(*buffer length *)
	val yybufpos: int ref = ref 1		(* location of next character to use *)
	val yygone: int ref = ref yygone0	(* position in file of beginning of buffer *)
	val yydone = ref false		(* eof found yet? *)
	val yybegin: int ref = ref 1		(*Current 'start state' for lexer *)

	val YYBEGIN = fn (Internal.StartStates.STARTSTATE x) =>
		 yybegin := x

fun lex (yyarg as (inputSource)) =
let fun continue() : Internal.result = 
  let fun scan (s,AcceptingLeaves : Internal.yyfinstate list list,l,i0: int) =
	let fun action (i: int,nil) = raise LexError
	| action (i,nil::l) = action (i-1,l)
	| action (i,(node::acts)::l) =
		case node of
		    Internal.N yyk => 
			(let fun yymktext() = String.substring(!yyb,i0,i-i0)
			     val yypos: int = i0+ !yygone
			open UserDeclarations Internal.StartStates
 in (yybufpos := i; case yyk of 

			(* Application actions *)

  100 => let val yytext=yymktext() in Add yytext; YYBEGIN STRING; continue() end
| 103 => let val yytext=yymktext() in Add yytext; continue() end
| 105 => let val yytext=yymktext() in Add yytext; continue() end
| 108 => let val yytext=yymktext() in Add yytext; dec commentLevel;
		    if !commentLevel=0
			 then BOGUS_VALUE(!lineno,!lineno)
			 else continue()
		    end
| 11 => let val yytext=yymktext() in Add yytext; continue() end
| 111 => let val yytext=yymktext() in Add yytext; inc commentLevel; continue() end
| 114 => let val yytext=yymktext() in Add yytext; continue() end
| 116 => (continue())
| 119 => (dec commentLevel;
		          if !commentLevel=0 then YYBEGIN A else ();
			  continue ())
| 122 => (inc commentLevel; continue())
| 125 => (continue())
| 127 => let val yytext=yymktext() in Add yytext; YYBEGIN CODE; continue() end
| 129 => let val yytext=yymktext() in Add yytext; continue() end
| 131 => let val yytext=yymktext() in Add yytext; error inputSource (!lineno) "unclosed string";
 	            inc lineno; YYBEGIN CODE; continue() end
| 134 => let val yytext=yymktext() in Add yytext; continue() end
| 137 => let val yytext=yymktext() in Add yytext; continue() end
| 14 => (YYBEGIN A; HEADER (concat (rev (!text)),!lineno,!lineno))
| 140 => let val yytext=yymktext() in Add yytext;
			if substring(yytext,1,1)="\n" then inc lineno else ();
		     	YYBEGIN F; continue() end
| 143 => let val yytext=yymktext() in Add yytext; continue() end
| 145 => let val yytext=yymktext() in Add yytext; YYBEGIN STRING; continue() end
| 147 => let val yytext=yymktext() in Add yytext; error inputSource (!lineno) "unclosed string";
		    YYBEGIN CODE; continue() end
| 16 => let val yytext=yymktext() in Add yytext; inc lineno; continue() end
| 18 => let val yytext=yymktext() in Add yytext; continue() end
| 2 => let val yytext=yymktext() in Add yytext; YYBEGIN COMMENT; commentLevel := 1;
		    continue(); YYBEGIN INITIAL; continue() end
| 20 => (inc lineno; continue ())
| 25 => (continue())
| 28 => (OF(!lineno,!lineno))
| 32 => (FOR(!lineno,!lineno))
| 34 => (LBRACE(!lineno,!lineno))
| 36 => (RBRACE(!lineno,!lineno))
| 38 => (COMMA(!lineno,!lineno))
| 40 => (ASTERISK(!lineno,!lineno))
| 43 => (ARROW(!lineno,!lineno))
| 49 => (PREC(Hdr.LEFT,!lineno,!lineno))
| 5 => (YYBEGIN EMPTYCOMMENT; commentLevel := 1; continue())
| 56 => (PREC(Hdr.RIGHT,!lineno,!lineno))
| 66 => (PREC(Hdr.NONASSOC,!lineno,!lineno))
| 70 => let val yytext=yymktext() in lookup(yytext,!lineno,!lineno) end
| 73 => let val yytext=yymktext() in TYVAR(yytext,!lineno,!lineno) end
| 77 => let val yytext=yymktext() in IDDOT(yytext,!lineno,!lineno) end
| 8 => let val yytext=yymktext() in Add yytext; YYBEGIN COMMENT; commentLevel := 1;
		    continue(); YYBEGIN CODE; continue() end
| 80 => let val yytext=yymktext() in INT (yytext,!lineno,!lineno) end
| 83 => (DELIMITER(!lineno,!lineno))
| 85 => (COLON(!lineno,!lineno))
| 87 => (BAR(!lineno,!lineno))
| 90 => let val yytext=yymktext() in ID ((yytext,!lineno),!lineno,!lineno) end
| 92 => (pcount := 1; actionstart := (!lineno);
		    text := nil; YYBEGIN CODE; continue() before YYBEGIN A)
| 94 => (DOT(!lineno,!lineno))
| 96 => let val yytext=yymktext() in inc pcount; Add yytext; continue() end
| 98 => let val yytext=yymktext() in dec pcount;
		    if !pcount = 0 then
			 PROG (concat (rev (!text)),!lineno,!lineno)
		    else (Add yytext; continue()) end
| _ => raise Internal.LexerError

		) end )

	val {fin,trans} = Vector.sub (Internal.tab, s)
	val NewAcceptingLeaves = fin::AcceptingLeaves
	in if l = !yybl then
	     if trans = #trans(Vector.sub(Internal.tab,0))
	       then action(l,NewAcceptingLeaves
) else	    let val newchars= if !yydone then "" else yyinput 1024
	    in if (String.size newchars)=0
		  then (yydone := true;
		        if (l=i0) then UserDeclarations.eof yyarg
		                  else action(l,NewAcceptingLeaves))
		  else (if i0=l then yyb := newchars
		     else yyb := String.substring(!yyb,i0,l-i0)^newchars;
		     yygone := !yygone+i0;
		     yybl := String.size (!yyb);
		     scan (s,AcceptingLeaves,l-i0,0))
	    end
	  else let val NewChar = Char.ord (CharVector.sub (!yyb,l))
		val NewChar = if NewChar<128 then NewChar else 128
		val NewState = Char.ord (CharVector.sub (trans,NewChar))
		in if NewState=0 then action(l,NewAcceptingLeaves)
		else scan(NewState,NewAcceptingLeaves,l+1,i0)
	end
	end
(*
	val start= if String.substring(!yyb,!yybufpos-1,1)="\n"
then !yybegin+1 else !yybegin
*)
	in scan(!yybegin (* start *),nil,!yybufpos,!yybufpos)
    end
in continue end
  in lex
  end
end
