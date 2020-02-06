structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val linenum = ref 1
val pos = ref 0
val eof = fn () => Tokens.EOF(!pos,!pos)

val to_int: string -> IntInf.int =
  foldl (fn(x,y)=>y*10+x) 0 o List.mapPartial (fn x => if Char.isDigit x then SOME (IntInf.fromInt (Char.ord x - Char.ord #"0")) else NONE) o explode;

fun is_hex_letter c = (c = #"a" orelse c = #"b" orelse c = #"c" orelse c = #"d" orelse c = #"e" orelse c = #"f")

val hex_to_int: string -> IntInf.int =
	foldl (fn(x,y)=>y*16+x) 0 o List.mapPartial (fn x => if Char.isDigit x then SOME (IntInf.fromInt (Char.ord x - Char.ord #"0")) else if is_hex_letter x then SOME (IntInf.fromInt (Char.ord x - Char.ord #"a" + 10)) else NONE) o explode;

fun suffix_len str: IntInf.int =
  IntInf.fromInt (case String.fields Char.isPunct str of [_] => 0 | [_,suf] => String.size suf)

%%
%header (functor x86_64LexFun(structure Tokens: x86_64_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t];
%%

".intel_syntax noprefix\n\n" => (Tokens.DOTINTEL(!pos,!pos));
".section"		=> (Tokens.DOTSECTION(!pos,!pos)); 
".align"			=> (Tokens.DOTALIGN(!pos,!pos)); 
".globl"			=> (Tokens.DOTGLOBL(!pos,!pos)); 
".type"				=> (Tokens.DOTTYPE(!pos,!pos)); 
".byte"				=> (Tokens.DOTBYTE(!pos,!pos)); 
".quad"				=> (Tokens.DOTQUAD(!pos,!pos)); 
".text"				=> (Tokens.DOTTEXT(!pos,!pos)); 
".data"				=> (Tokens.DOTDATA(!pos,!pos)); 
".rodata"			=> (Tokens.DOTRODATA(!pos,!pos)); 
".bss"				=> (Tokens.DOTBSS(!pos,!pos)); 
".init"				=> (Tokens.DOTINIT(!pos,!pos)); 
".comment"		=> (Tokens.DOTCOMMENT(!pos,!pos)); 
".symtab"			=> (Tokens.DOTSYMTAB(!pos,!pos)); 
".shstrtab"		=> (Tokens.DOTSHSTRTAB(!pos,!pos)); 
".strtab"			=> (Tokens.DOTSTRTAB(!pos,!pos)); 


"aaa" => (Tokens.AAA(!pos,!pos));
"aad" => (Tokens.AAD(!pos,!pos));
"aam" => (Tokens.AAM(!pos,!pos));
"aas" => (Tokens.AAS(!pos,!pos));"adc" => (Tokens.ADC(!pos,!pos));"add" => (Tokens.ADD(!pos,!pos));
"and" => (Tokens.AND(!pos,!pos));"call" => (Tokens.CALL(!pos,!pos));"cbw" => (Tokens.CBW(!pos,!pos));
"clc" => (Tokens.CLC(!pos,!pos));"cld" => (Tokens.CLD(!pos,!pos));"cli" => (Tokens.CLI(!pos,!pos));
"cmc" => (Tokens.CMC(!pos,!pos));"cmp" => (Tokens.CMP(!pos,!pos));"cmpsb" => (Tokens.CMPSB(!pos,!pos));
"cwd" => (Tokens.CWD(!pos,!pos));"daa" => (Tokens.DAA(!pos,!pos));"das" => (Tokens.DAS(!pos,!pos));
"dec" => (Tokens.DEC(!pos,!pos));"div" => (Tokens.DIV(!pos,!pos));"esc" => (Tokens.ESC(!pos,!pos));
"hlt" => (Tokens.HLT(!pos,!pos));"idiv" => (Tokens.IDIV(!pos,!pos));"imul" => (Tokens.IMUL(!pos,!pos));
"in" => (Tokens.IN(!pos,!pos));"inc" => (Tokens.INC(!pos,!pos));
"int" => (Tokens.INT(!pos,!pos));"into" => (Tokens.INTO(!pos,!pos));"iret" => (Tokens.IRET(!pos,!pos));"ja" => (Tokens.JA(!pos,!pos));
"jae" => (Tokens.JAE(!pos,!pos));"jb" => (Tokens.JB(!pos,!pos));"jbe" => (Tokens.JBE(!pos,!pos));"jc" => (Tokens.JC(!pos,!pos));
"je" => (Tokens.JE(!pos,!pos));"jg" => (Tokens.JG(!pos,!pos));"jge" => (Tokens.JGE(!pos,!pos));"jl" => (Tokens.JL(!pos,!pos));
"jle" => (Tokens.JLE(!pos,!pos));"jna" => (Tokens.JNA(!pos,!pos));"jnae" => (Tokens.JNAE(!pos,!pos));"jnb" => (Tokens.JNB(!pos,!pos));
"jnbe" => (Tokens.JNBE(!pos,!pos));"jnc" => (Tokens.JNC(!pos,!pos));"jne" => (Tokens.JNE(!pos,!pos));"jng" => (Tokens.JNG(!pos,!pos));
"jnge" => (Tokens.JNGE(!pos,!pos));"jnl" => (Tokens.JNL(!pos,!pos));"jnle" => (Tokens.JNLE(!pos,!pos));
"jno" => (Tokens.JNO(!pos,!pos));"jnp" => (Tokens.JNP(!pos,!pos));"jns" => (Tokens.JNS(!pos,!pos));
"jnz" => (Tokens.JNZ(!pos,!pos));"jo" => (Tokens.JO(!pos,!pos));"jp" => (Tokens.JP(!pos,!pos));"jpe" => (Tokens.JPE(!pos,!pos));
"jpo" => (Tokens.JPO(!pos,!pos));"js" => (Tokens.JS(!pos,!pos));"jz" => (Tokens.JZ(!pos,!pos));"jmp" => (Tokens.JMP(!pos,!pos));
"lahf" => (Tokens.LAHF(!pos,!pos));"lds" => (Tokens.LDS(!pos,!pos));"lea" => (Tokens.LEA(!pos,!pos));"les" => (Tokens.LES(!pos,!pos));
"lock" => (Tokens.LOCK(!pos,!pos));"lodsb" => (Tokens.LODSB(!pos,!pos));"lodsw" => (Tokens.LODSW(!pos,!pos));
"loop" => (Tokens.LOOP(!pos,!pos));"loope" => (Tokens.LOOPE(!pos,!pos));"loopne" => (Tokens.LOOPNE(!pos,!pos));
"loopnz" => (Tokens.LOOPNZ(!pos,!pos));"loopz" => (Tokens.LOOPZ(!pos,!pos));"mov" => (Tokens.MOV(!pos,!pos));
"movsb" => (Tokens.MOVSB(!pos,!pos));"movsw" => (Tokens.MOVSW(!pos,!pos));"mul" => (Tokens.MUL(!pos,!pos));
"neg" => (Tokens.NEG(!pos,!pos));"nop" => (Tokens.NOP(!pos,!pos));"not" => (Tokens.NOT(!pos,!pos));"or" => (Tokens.OR(!pos,!pos));
"out" => (Tokens.OUT(!pos,!pos));"pop" => (Tokens.POP(!pos,!pos));"popf" => (Tokens.POPF(!pos,!pos));
"push" => (Tokens.PUSH(!pos,!pos));"pushf" => (Tokens.PUSHF(!pos,!pos));"rcl" => (Tokens.RCL(!pos,!pos));
"rcr" => (Tokens.RCR(!pos,!pos));"ret" => (Tokens.RET(!pos,!pos));"retn" => (Tokens.RETN(!pos,!pos));
"retf" => (Tokens.RETF(!pos,!pos));"rol" => (Tokens.ROL(!pos,!pos));"ror" => (Tokens.ROR(!pos,!pos));
"sahf" => (Tokens.SAHF(!pos,!pos));"sal" => (Tokens.SAL(!pos,!pos));"sar" => (Tokens.SAR(!pos,!pos));
"sbb" => (Tokens.SBB(!pos,!pos));"scasb" => (Tokens.SCASB(!pos,!pos));"scasw" => (Tokens.SCASW(!pos,!pos));
"shl" => (Tokens.SHL(!pos,!pos));"shr" => (Tokens.SHR(!pos,!pos));"stc" => (Tokens.STC(!pos,!pos));
"std" => (Tokens.STD(!pos,!pos));"sti" => (Tokens.STI(!pos,!pos));"stosb" => (Tokens.STOSB(!pos,!pos));
"stosw" => (Tokens.STOSW(!pos,!pos));"sub" => (Tokens.SUB(!pos,!pos));"test" => (Tokens.TEST(!pos,!pos));
"wait" => (Tokens.WAIT(!pos,!pos));"xchg" => (Tokens.XCHG(!pos,!pos));"xlat" => (Tokens.XLAT(!pos,!pos));
"xor" => (Tokens.XOR(!pos,!pos));

"rep" => (Tokens.REP(!pos,!pos));"repe" => (Tokens.REPE(!pos,!pos));"repne" => (Tokens.REPNE(!pos,!pos));
"repnz" => (Tokens.REPNZ(!pos,!pos));"repz" => (Tokens.REPZ(!pos,!pos));

"movs" => (Tokens.MOVS(!pos,!pos));"stos" => (Tokens.STOS(!pos,!pos));"cmps" => (Tokens.CMPS(!pos,!pos));
"lods" => (Tokens.LODS(!pos,!pos));"scas" => (Tokens.SCAS(!pos,!pos));



"f2xm1" => (Tokens.F2XM1(!pos,!pos));"fabs" => (Tokens.FABS(!pos,!pos));"fadd" => (Tokens.FADD(!pos,!pos));
"faddp" => (Tokens.FADDP(!pos,!pos));"fbld" => (Tokens.FBLD(!pos,!pos));"fbstp" => (Tokens.FBSTP(!pos,!pos));
"fchs" => (Tokens.FCHS(!pos,!pos));"fclex" => (Tokens.FCLEX(!pos,!pos));"fcom" => (Tokens.FCOM(!pos,!pos));
"fcomp" => (Tokens.FCOMP(!pos,!pos));"fcompp" => (Tokens.FCOMPP(!pos,!pos));"decstp" => (Tokens.DECSTP(!pos,!pos));
"fdisi" => (Tokens.FDISI(!pos,!pos));"fdiv" => (Tokens.FDIV(!pos,!pos));"fdivp" => (Tokens.FDIVP(!pos,!pos));
"fdivr" => (Tokens.FDIVR(!pos,!pos));"fdivrp" => (Tokens.FDIVRP(!pos,!pos));"feni" => (Tokens.FENI(!pos,!pos));
"ffree" => (Tokens.FFREE(!pos,!pos));"fiadd" => (Tokens.FIADD(!pos,!pos));"ficom" => (Tokens.FICOM(!pos,!pos));
"ficomp" => (Tokens.FICOMP(!pos,!pos));"fidiv" => (Tokens.FIDIV(!pos,!pos));"fidivr" => (Tokens.FIDIVR(!pos,!pos));
"fild" => (Tokens.FILD(!pos,!pos));"fimul" => (Tokens.FIMUL(!pos,!pos));"fincstp" => (Tokens.FINCSTP(!pos,!pos));
"finit" => (Tokens.FINIT(!pos,!pos));"fist" => (Tokens.FIST(!pos,!pos));"fistp" => (Tokens.FISTP(!pos,!pos));
"fisub" => (Tokens.FISUB(!pos,!pos));"isubr" => (Tokens.ISUBR(!pos,!pos));"fld" => (Tokens.FLD(!pos,!pos));
"fld1" => (Tokens.FLD1(!pos,!pos));"fldcw" => (Tokens.FLDCW(!pos,!pos));"fldenv" => (Tokens.FLDENV(!pos,!pos));
"fldenvw" => (Tokens.FLDENVW(!pos,!pos));"fldl2e" => (Tokens.FLDL2E(!pos,!pos));"fldl2t" => (Tokens.FLDL2T(!pos,!pos));
"fldlg2" => (Tokens.FLDLG2(!pos,!pos));"fldln2" => (Tokens.FLDLN2(!pos,!pos));"ldpi" => (Tokens.LDPI(!pos,!pos));
"fldz" => (Tokens.FLDZ(!pos,!pos));"fmul" => (Tokens.FMUL(!pos,!pos));"fmulp" => (Tokens.FMULP(!pos,!pos));
"fnclex" => (Tokens.FNCLEX(!pos,!pos));"fndisi" => (Tokens.FNDISI(!pos,!pos));"fneni" => (Tokens.FNENI(!pos,!pos));
"fninit" => (Tokens.FNINIT(!pos,!pos));"fnop" => (Tokens.FNOP(!pos,!pos));"fnsave" => (Tokens.FNSAVE(!pos,!pos));
"fnsavew" => (Tokens.FNSAVEW(!pos,!pos));"fnstcw" => (Tokens.FNSTCW(!pos,!pos));"fnstenv" => (Tokens.FNSTENV(!pos,!pos));
"fnstenvw" => (Tokens.FNSTENVW(!pos,!pos));"fnstsw" => (Tokens.FNSTSW(!pos,!pos));"fpatan" => (Tokens.FPATAN(!pos,!pos));
"fprem" => (Tokens.FPREM(!pos,!pos));"fptan" => (Tokens.FPTAN(!pos,!pos));"frndint" => (Tokens.FRNDINT(!pos,!pos));
"frstor" => (Tokens.FRSTOR(!pos,!pos));"frstorw" => (Tokens.FRSTORW(!pos,!pos));"save" => (Tokens.SAVE(!pos,!pos));
"fsavew" => (Tokens.FSAVEW(!pos,!pos));"fscale" => (Tokens.FSCALE(!pos,!pos));"fsqrt" => (Tokens.FSQRT(!pos,!pos));
"fst" => (Tokens.FST(!pos,!pos));"fstcw" => (Tokens.FSTCW(!pos,!pos));"fstenv" => (Tokens.FSTENV(!pos,!pos));
"fstenvw" => (Tokens.FSTENVW(!pos,!pos));"fstp" => (Tokens.FSTP(!pos,!pos));"fstsw" => (Tokens.FSTSW(!pos,!pos));
"fsub" => (Tokens.FSUB(!pos,!pos));"fsubp" => (Tokens.FSUBP(!pos,!pos));"fsubr" => (Tokens.FSUBR(!pos,!pos));
"fsubrp" => (Tokens.FSUBRP(!pos,!pos));"ftst" => (Tokens.FTST(!pos,!pos));"fwait" => (Tokens.FWAIT(!pos,!pos));
"fxam" => (Tokens.FXAM(!pos,!pos));"fxch" => (Tokens.FXCH(!pos,!pos));"fxtract" => (Tokens.FXTRACT(!pos,!pos));
"fyl2x" => (Tokens.FYL2X(!pos,!pos));"fyl2xp1" => (Tokens.FYL2XP1(!pos,!pos));

"bound" => (Tokens.BOUND(!pos,!pos));"enter" => (Tokens.ENTER(!pos,!pos));"ins" => (Tokens.INS(!pos,!pos));
"leave" => (Tokens.LEAVE(!pos,!pos));"outs" => (Tokens.OUTS(!pos,!pos));"popa" => (Tokens.POPA(!pos,!pos));
"pusha" => (Tokens.PUSHA(!pos,!pos));

"arpl" => (Tokens.ARPL(!pos,!pos));"clts" => (Tokens.CLTS(!pos,!pos));"lar" => (Tokens.LAR(!pos,!pos));
"lgdt" => (Tokens.LGDT(!pos,!pos));"lidt" => (Tokens.LIDT(!pos,!pos));"lldt" => (Tokens.LLDT(!pos,!pos));
"lmsw" => (Tokens.LMSW(!pos,!pos));"loadall" => (Tokens.LOADALL(!pos,!pos));"lsl" => (Tokens.LSL(!pos,!pos));
"ltr" => (Tokens.LTR(!pos,!pos));"sgdt" => (Tokens.SGDT(!pos,!pos));"sidt" => (Tokens.SIDT(!pos,!pos));
"sldt" => (Tokens.SLDT(!pos,!pos));"smsw" => (Tokens.SMSW(!pos,!pos));"str" => (Tokens.STR(!pos,!pos));
"verr" => (Tokens.VERR(!pos,!pos));"verw" => (Tokens.VERW(!pos,!pos));

"fsetpm" => (Tokens.FSETPM(!pos,!pos));

"bsf" => (Tokens.BSF(!pos,!pos));"bsr" => (Tokens.BSR(!pos,!pos));"bt" => (Tokens.BT(!pos,!pos));"btc" => (Tokens.BTC(!pos,!pos));
"btr" => (Tokens.BTR(!pos,!pos));"bts" => (Tokens.BTS(!pos,!pos));"cdq" => (Tokens.CDQ(!pos,!pos));"cwde" => (Tokens.CWDE(!pos,!pos));
"ibts" => (Tokens.IBTS(!pos,!pos));"insd" => (Tokens.INSD(!pos,!pos));"iretd" => (Tokens.IRETD(!pos,!pos));
"iretf" => (Tokens.IRETF(!pos,!pos));"jecxz" => (Tokens.JECXZ(!pos,!pos));"lfs" => (Tokens.LFS(!pos,!pos));
"lgs" => (Tokens.LGS(!pos,!pos));"lss" => (Tokens.LSS(!pos,!pos));"lodsd" => (Tokens.LODSD(!pos,!pos));
"loopw" => (Tokens.LOOPW(!pos,!pos));"loopzw" => (Tokens.LOOPZW(!pos,!pos));"loopew" => (Tokens.LOOPEW(!pos,!pos));
"loopnzw" => (Tokens.LOOPNZW(!pos,!pos));"loopnew" => (Tokens.LOOPNEW(!pos,!pos));"loopd" => (Tokens.LOOPD(!pos,!pos));
"loopzd" => (Tokens.LOOPZD(!pos,!pos));"looped" => (Tokens.LOOPED(!pos,!pos));"loopnzd" => (Tokens.LOOPNZD(!pos,!pos));
"loopned" => (Tokens.LOOPNED(!pos,!pos));"movsx" => (Tokens.MOVSX(!pos,!pos));"movzx" => (Tokens.MOVZX(!pos,!pos));
"outsd" => (Tokens.OUTSD(!pos,!pos));"popad" => (Tokens.POPAD(!pos,!pos));"popfd" => (Tokens.POPFD(!pos,!pos));
"pushad" => (Tokens.PUSHAD(!pos,!pos));"pushfd" => (Tokens.PUSHFD(!pos,!pos));"scasd" => (Tokens.SCASD(!pos,!pos));
"seta" => (Tokens.SETA(!pos,!pos));"setae" => (Tokens.SETAE(!pos,!pos));"setb" => (Tokens.SETB(!pos,!pos));
"setbe" => (Tokens.SETBE(!pos,!pos));"setc" => (Tokens.SETC(!pos,!pos));"sete" => (Tokens.SETE(!pos,!pos));
"setg" => (Tokens.SETG(!pos,!pos));"setge" => (Tokens.SETGE(!pos,!pos));"setl" => (Tokens.SETL(!pos,!pos));
"setle" => (Tokens.SETLE(!pos,!pos));"setna" => (Tokens.SETNA(!pos,!pos));"setnae" => (Tokens.SETNAE(!pos,!pos));
"setnb" => (Tokens.SETNB(!pos,!pos));"setnbe" => (Tokens.SETNBE(!pos,!pos));"setnc" => (Tokens.SETNC(!pos,!pos));
"setne" => (Tokens.SETNE(!pos,!pos));"setng" => (Tokens.SETNG(!pos,!pos));"setnge" => (Tokens.SETNGE(!pos,!pos));
"setnl" => (Tokens.SETNL(!pos,!pos));"setnle" => (Tokens.SETNLE(!pos,!pos));"setno" => (Tokens.SETNO(!pos,!pos));
"setnp" => (Tokens.SETNP(!pos,!pos));"setns" => (Tokens.SETNS(!pos,!pos));"setnz" => (Tokens.SETNZ(!pos,!pos));
"seto" => (Tokens.SETO(!pos,!pos));"setp" => (Tokens.SETP(!pos,!pos));"setpe" => (Tokens.SETPE(!pos,!pos));
"setpo" => (Tokens.SETPO(!pos,!pos));"sets" => (Tokens.SETS(!pos,!pos));"setz" => (Tokens.SETZ(!pos,!pos));

"fcos" => (Tokens.FCOS(!pos,!pos));"fldenvd" => (Tokens.FLDENVD(!pos,!pos));"fsaved" => (Tokens.FSAVED(!pos,!pos));
"fstenvd" => (Tokens.FSTENVD(!pos,!pos));"fprem1" => (Tokens.FPREM1(!pos,!pos));"frstord" => (Tokens.FRSTORD(!pos,!pos));
"fsin" => (Tokens.FSIN(!pos,!pos));"fsincos" => (Tokens.FSINCOS(!pos,!pos));"fucom" => (Tokens.FUCOM(!pos,!pos));
"fucomp" => (Tokens.FUCOMP(!pos,!pos));"fucompp" => (Tokens.FUCOMPP(!pos,!pos));

"bswap" => (Tokens.BSWAP(!pos,!pos));"cmpxchg" => (Tokens.CMPXCHG(!pos,!pos));"invd" => (Tokens.INVD(!pos,!pos));
"invlpg" => (Tokens.INVLPG(!pos,!pos));"wbinvd" => (Tokens.WBINVD(!pos,!pos));"xadd" => (Tokens.XADD(!pos,!pos));

"cpuid" => (Tokens.CPUID(!pos,!pos));"cmpxchg8b" => (Tokens.CMPXCHG8B(!pos,!pos));"rdmsr" => (Tokens.RDMSR(!pos,!pos));
"rdtsc" => (Tokens.RDTSC(!pos,!pos));"wrmsr" => (Tokens.WRMSR(!pos,!pos));"rsm" => (Tokens.RSM(!pos,!pos));

"rdpmc" => (Tokens.RDPMC(!pos,!pos));

"emms" => (Tokens.EMMS(!pos,!pos));"movd" => (Tokens.MOVD(!pos,!pos));"movq" => (Tokens.MOVQ(!pos,!pos));
"packssdw" => (Tokens.PACKSSDW(!pos,!pos));"packsswb" => (Tokens.PACKSSWB(!pos,!pos));
"packuswb" => (Tokens.PACKUSWB(!pos,!pos));"paddb" => (Tokens.PADDB(!pos,!pos));"paddw" => (Tokens.PADDW(!pos,!pos));
"paddd" => (Tokens.PADDD(!pos,!pos));"paddq" => (Tokens.PADDQ(!pos,!pos));"paddsb" => (Tokens.PADDSB(!pos,!pos));
"paddsw" => (Tokens.PADDSW(!pos,!pos));"paddusb" => (Tokens.PADDUSB(!pos,!pos));"paddusw" => (Tokens.PADDUSW(!pos,!pos));
"pand" => (Tokens.PAND(!pos,!pos));"pandn" => (Tokens.PANDN(!pos,!pos));"por" => (Tokens.POR(!pos,!pos));
"pxor" => (Tokens.PXOR(!pos,!pos));"pcmpeqb" => (Tokens.PCMPEQB(!pos,!pos));"pcmpeqw" => (Tokens.PCMPEQW(!pos,!pos));
"pcmpeqd" => (Tokens.PCMPEQD(!pos,!pos));"pcmpgtb" => (Tokens.PCMPGTB(!pos,!pos));"pcmpgtw" => (Tokens.PCMPGTW(!pos,!pos));
"pcmpgtd" => (Tokens.PCMPGTD(!pos,!pos));"pmaddwd" => (Tokens.PMADDWD(!pos,!pos));"pmulhw" => (Tokens.PMULHW(!pos,!pos));
"pmullw" => (Tokens.PMULLW(!pos,!pos));"psllw" => (Tokens.PSLLW(!pos,!pos));"pslld" => (Tokens.PSLLD(!pos,!pos));
"psllq" => (Tokens.PSLLQ(!pos,!pos));"psrad" => (Tokens.PSRAD(!pos,!pos));"psraw" => (Tokens.PSRAW(!pos,!pos));
"psrlw" => (Tokens.PSRLW(!pos,!pos));"psrld" => (Tokens.PSRLD(!pos,!pos));"psrlq" => (Tokens.PSRLQ(!pos,!pos));
"psubb" => (Tokens.PSUBB(!pos,!pos));"psubw" => (Tokens.PSUBW(!pos,!pos));"psubd" => (Tokens.PSUBD(!pos,!pos));
"psubsb" => (Tokens.PSUBSB(!pos,!pos));"psubsw" => (Tokens.PSUBSW(!pos,!pos));"psubusb" => (Tokens.PSUBUSB(!pos,!pos));
"psubusw" => (Tokens.PSUBUSW(!pos,!pos));"punpckhbw" => (Tokens.PUNPCKHBW(!pos,!pos));
"punpckhwd" => (Tokens.PUNPCKHWD(!pos,!pos));"punpckhdq" => (Tokens.PUNPCKHDQ(!pos,!pos));
"punpcklbw" => (Tokens.PUNPCKLBW(!pos,!pos));"punpcklwd" => (Tokens.PUNPCKLWD(!pos,!pos));"punpckldq" => (Tokens.PUNPCKLDQ(!pos,!pos));

"cmova" => (Tokens.CMOVA(!pos,!pos));"cmovae" => (Tokens.CMOVAE(!pos,!pos));"cmovb" => (Tokens.CMOVB(!pos,!pos));
"cmovbe" => (Tokens.CMOVBE(!pos,!pos));"cmovc" => (Tokens.CMOVC(!pos,!pos));"cmove" => (Tokens.CMOVE(!pos,!pos));
"cmovg" => (Tokens.CMOVG(!pos,!pos));"cmovge" => (Tokens.CMOVGE(!pos,!pos));"cmovl" => (Tokens.CMOVL(!pos,!pos));
"cmovle" => (Tokens.CMOVLE(!pos,!pos));"cmovna" => (Tokens.CMOVNA(!pos,!pos));"cmovnae" => (Tokens.CMOVNAE(!pos,!pos));
"cmovnb" => (Tokens.CMOVNB(!pos,!pos));"cmovnbe" => (Tokens.CMOVNBE(!pos,!pos));"cmovnc" => (Tokens.CMOVNC(!pos,!pos));
"cmovne" => (Tokens.CMOVNE(!pos,!pos));"cmovng" => (Tokens.CMOVNG(!pos,!pos));"cmovnge" => (Tokens.CMOVNGE(!pos,!pos));
"cmovnl" => (Tokens.CMOVNL(!pos,!pos));"cmovnle" => (Tokens.CMOVNLE(!pos,!pos));"cmovno" => (Tokens.CMOVNO(!pos,!pos));
"cmovnp" => (Tokens.CMOVNP(!pos,!pos));"cmovns" => (Tokens.CMOVNS(!pos,!pos));"cmovnz" => (Tokens.CMOVNZ(!pos,!pos));
"cmovo" => (Tokens.CMOVO(!pos,!pos));"cmovp" => (Tokens.CMOVP(!pos,!pos));"cmovpe" => (Tokens.CMOVPE(!pos,!pos));
"cmovpo" => (Tokens.CMOVPO(!pos,!pos));"cmovs" => (Tokens.CMOVS(!pos,!pos));"cmovz" => (Tokens.CMOVZ(!pos,!pos));
"ud2" => (Tokens.UD2(!pos,!pos));

"fcmovb" => (Tokens.FCMOVB(!pos,!pos));"fcmovbe" => (Tokens.FCMOVBE(!pos,!pos));"fcmove" => (Tokens.FCMOVE(!pos,!pos));
"fcmovnb" => (Tokens.FCMOVNB(!pos,!pos));"fcmovnbe" => (Tokens.FCMOVNBE(!pos,!pos));"fcmovne" => (Tokens.FCMOVNE(!pos,!pos));
"fcmovnu" => (Tokens.FCMOVNU(!pos,!pos));"fcmovu" => (Tokens.FCMOVU(!pos,!pos));"fcomi" => (Tokens.FCOMI(!pos,!pos));
"fcomip" => (Tokens.FCOMIP(!pos,!pos));"fucomi" => (Tokens.FUCOMI(!pos,!pos));"fucomip" => (Tokens.FUCOMIP(!pos,!pos));

"sysenter" => (Tokens.SYSENTER(!pos,!pos));"sysexit" => (Tokens.SYSEXIT(!pos,!pos));

"maskmovq" => (Tokens.MASKMOVQ(!pos,!pos));"movntq" => (Tokens.MOVNTQ(!pos,!pos));"prefetcht0" => (Tokens.PREFETCHT0(!pos,!pos));
"prefetcht1" => (Tokens.PREFETCHT1(!pos,!pos));"prefetcht2" => (Tokens.PREFETCHT2(!pos,!pos));"prefetchnta" => (Tokens.PREFETCHNTA(!pos,!pos));
"sfence" => (Tokens.SFENCE(!pos,!pos));

"fxrstor" => (Tokens.FXRSTOR(!pos,!pos));"fxsave" => (Tokens.FXSAVE(!pos,!pos));

"pshufw" => (Tokens.PSHUFW(!pos,!pos));"pinsrw" => (Tokens.PINSRW(!pos,!pos));"pextrw" => (Tokens.PEXTRW(!pos,!pos));
"pmovmskb" => (Tokens.PMOVMSKB(!pos,!pos));"pminub" => (Tokens.PMINUB(!pos,!pos));"pmaxub" => (Tokens.PMAXUB(!pos,!pos));
"pavgb" => (Tokens.PAVGB(!pos,!pos));"pavgw" => (Tokens.PAVGW(!pos,!pos));"pmulhuw" => (Tokens.PMULHUW(!pos,!pos));
"pminsw" => (Tokens.PMINSW(!pos,!pos));"pmaxsw" => (Tokens.PMAXSW(!pos,!pos));"psadbw" => (Tokens.PSADBW(!pos,!pos));

"andps" => (Tokens.ANDPS(!pos,!pos));
"andnps" => (Tokens.ANDNPS(!pos,!pos));"orps" => (Tokens.ORPS(!pos,!pos));"xorps" => (Tokens.XORPS(!pos,!pos));
"movups" => (Tokens.MOVUPS(!pos,!pos));"movss" => (Tokens.MOVSS(!pos,!pos));"movhlps" => (Tokens.MOVHLPS(!pos,!pos));
"movlps" => (Tokens.MOVLPS(!pos,!pos));"unpcklps" => (Tokens.UNPCKLPS(!pos,!pos));"unpckhps" => (Tokens.UNPCKHPS(!pos,!pos));
"movlhps" => (Tokens.MOVLHPS(!pos,!pos));"movhps" => (Tokens.MOVHPS(!pos,!pos));"movaps" => (Tokens.MOVAPS(!pos,!pos));
"movmskps" => (Tokens.MOVMSKPS(!pos,!pos));"cvtpi2ps" => (Tokens.CVTPI2PS(!pos,!pos));"cvtsi2ss" => (Tokens.CVTSI2SS(!pos,!pos));
"movntps" => (Tokens.MOVNTPS(!pos,!pos));"cvttps2pi" => (Tokens.CVTTPS2PI(!pos,!pos));"cvttss2si" => (Tokens.CVTTSS2SI(!pos,!pos));
"cvtps2pi" => (Tokens.CVTPS2PI(!pos,!pos));"cvtss2si" => (Tokens.CVTSS2SI(!pos,!pos));"ucomiss" => (Tokens.UCOMISS(!pos,!pos));
"comiss" => (Tokens.COMISS(!pos,!pos));"sqrtps" => (Tokens.SQRTPS(!pos,!pos));"sqrtss" => (Tokens.SQRTSS(!pos,!pos));
"rsqrtps" => (Tokens.RSQRTPS(!pos,!pos));"rsqrtss" => (Tokens.RSQRTSS(!pos,!pos));"rcpps" => (Tokens.RCPPS(!pos,!pos));
"rcpss" => (Tokens.RCPSS(!pos,!pos));"addps" => (Tokens.ADDPS(!pos,!pos));"addss" => (Tokens.ADDSS(!pos,!pos));
"mulps" => (Tokens.MULPS(!pos,!pos));"mulss" => (Tokens.MULSS(!pos,!pos));"subps" => (Tokens.SUBPS(!pos,!pos));
"subss" => (Tokens.SUBSS(!pos,!pos));"minps" => (Tokens.MINPS(!pos,!pos));"minss" => (Tokens.MINSS(!pos,!pos));
"divps" => (Tokens.DIVPS(!pos,!pos));"divss" => (Tokens.DIVSS(!pos,!pos));"maxps" => (Tokens.MAXPS(!pos,!pos));
"maxss" => (Tokens.MAXSS(!pos,!pos));"ldmxcsr" => (Tokens.LDMXCSR(!pos,!pos));"stmxcsr" => (Tokens.STMXCSR(!pos,!pos));
"cmpps" => (Tokens.CMPPS(!pos,!pos));"cmpss" => (Tokens.CMPSS(!pos,!pos));"shufps" => (Tokens.SHUFPS(!pos,!pos));

"clflush" => (Tokens.CLFLUSH(!pos,!pos));"lfence" => (Tokens.LFENCE(!pos,!pos));"mfence" => (Tokens.MFENCE(!pos,!pos));
"movnti" => (Tokens.MOVNTI(!pos,!pos));"pause" => (Tokens.PAUSE(!pos,!pos));

"psubq" => (Tokens.PSUBQ(!pos,!pos));"pmuludq" => (Tokens.PMULUDQ(!pos,!pos));

"movabs" => (Tokens.MOV(!pos,!pos));
"movapd" => (Tokens.MOVAPD(!pos,!pos));"movntpd" => (Tokens.MOVNTPD(!pos,!pos));"movhpd" => (Tokens.MOVHPD(!pos,!pos));
"movlpd" => (Tokens.MOVLPD(!pos,!pos));"movupd" => (Tokens.MOVUPD(!pos,!pos));"movmskpd" => (Tokens.MOVMSKPD(!pos,!pos));
"movsd" => (Tokens.MOVSD(!pos,!pos));"addpd" => (Tokens.ADDPD(!pos,!pos));"addsd" => (Tokens.ADDSD(!pos,!pos));
"divpd" => (Tokens.DIVPD(!pos,!pos));"divsd" => (Tokens.DIVSD(!pos,!pos));"maxpd" => (Tokens.MAXPD(!pos,!pos));
"maxsd" => (Tokens.MAXSD(!pos,!pos));"minpd" => (Tokens.MINPD(!pos,!pos));"minsd" => (Tokens.MINSD(!pos,!pos));
"mulpd" => (Tokens.MULPD(!pos,!pos));"mulsd" => (Tokens.MULSD(!pos,!pos));"sqrtpd" => (Tokens.SQRTPD(!pos,!pos));
"sqrtsd" => (Tokens.SQRTSD(!pos,!pos));"subpd" => (Tokens.SUBPD(!pos,!pos));"subsd" => (Tokens.SUBSD(!pos,!pos));
"andpd" => (Tokens.ANDPD(!pos,!pos));"andnpd" => (Tokens.ANDNPD(!pos,!pos));"orpd" => (Tokens.ORPD(!pos,!pos));
"xorpd" => (Tokens.XORPD(!pos,!pos));"cmppd" => (Tokens.CMPPD(!pos,!pos));"cmpsd" => (Tokens.CMPSD(!pos,!pos));
"comisd" => (Tokens.COMISD(!pos,!pos));"ucomisd" => (Tokens.UCOMISD(!pos,!pos));"shufpd" => (Tokens.SHUFPD(!pos,!pos));
"unpckhpd" => (Tokens.UNPCKHPD(!pos,!pos));"unpcklpd" => (Tokens.UNPCKLPD(!pos,!pos));"cvtdq2pd" => (Tokens.CVTDQ2PD(!pos,!pos));
"cvtdq2ps" => (Tokens.CVTDQ2PS(!pos,!pos));"cvtpd2dq" => (Tokens.CVTPD2DQ(!pos,!pos));"cvtpd2pi" => (Tokens.CVTPD2PI(!pos,!pos));
"cvtpd2ps" => (Tokens.CVTPD2PS(!pos,!pos));"cvtpi2pd" => (Tokens.CVTPI2PD(!pos,!pos));"cvtps2dq" => (Tokens.CVTPS2DQ(!pos,!pos));
"cvtps2pd" => (Tokens.CVTPS2PD(!pos,!pos));"cvtsd2si" => (Tokens.CVTSD2SI(!pos,!pos));"cvtsd2ss" => (Tokens.CVTSD2SS(!pos,!pos));
"cvtsi2sd" => (Tokens.CVTSI2SD(!pos,!pos));"cvtss2sd" => (Tokens.CVTSS2SD(!pos,!pos));"cvttpd2dq" => (Tokens.CVTTPD2DQ(!pos,!pos));
"cvttpd2pi" => (Tokens.CVTTPD2PI(!pos,!pos));"cvttps2dq" => (Tokens.CVTTPS2DQ(!pos,!pos));
"cvttsd2si" => (Tokens.CVTTSD2SI(!pos,!pos));"maskmovdqu" => (Tokens.MASKMOVDQU(!pos,!pos));"movdq2q" => (Tokens.MOVDQ2Q(!pos,!pos));
"movdqa" => (Tokens.MOVDQA(!pos,!pos));"movdqu" => (Tokens.MOVDQU(!pos,!pos));"movq2dq" => (Tokens.MOVQ2DQ(!pos,!pos));
"movntdq" => (Tokens.MOVNTDQ(!pos,!pos));"pshufhw" => (Tokens.PSHUFHW(!pos,!pos));"pshuflw" => (Tokens.PSHUFLW(!pos,!pos));
"pshufd" => (Tokens.PSHUFD(!pos,!pos));"pslldq" => (Tokens.PSLLDQ(!pos,!pos));"psrldq" => (Tokens.PSRLDQ(!pos,!pos));
"punpckhqdq" => (Tokens.PUNPCKHQDQ(!pos,!pos));"punpcklqdq" => (Tokens.PUNPCKLQDQ(!pos,!pos));

"cdqe" => (Tokens.CDQE(!pos,!pos));"cqo" => (Tokens.CQO(!pos,!pos));"cmpsq" => (Tokens.CMPSQ(!pos,!pos));
"cmpxchg16b" => (Tokens.CMPXCHG16B(!pos,!pos));"iretq" => (Tokens.IRETQ(!pos,!pos));"jrcxz" => (Tokens.JRCXZ(!pos,!pos));
"lodsq" => (Tokens.LODSQ(!pos,!pos));"movsxd" => (Tokens.MOVSXD(!pos,!pos));"popfq" => (Tokens.POPFQ(!pos,!pos));
"pushfq" => (Tokens.PUSHFQ(!pos,!pos));"rdtscp" => (Tokens.RDTSCP(!pos,!pos));"scasq" => (Tokens.SCASQ(!pos,!pos));
"stosq" => (Tokens.STOSQ(!pos,!pos));"swapgs" => (Tokens.SWAPGS(!pos,!pos));

"monitor" => (Tokens.MONITOR(!pos,!pos));"mwait" => (Tokens.MWAIT(!pos,!pos));

"fisttp" => (Tokens.FISTTP(!pos,!pos));

"addsubps" => (Tokens.ADDSUBPS(!pos,!pos));"addsubpd" => (Tokens.ADDSUBPD(!pos,!pos));"movddup" => (Tokens.MOVDDUP(!pos,!pos));
"movsldup" => (Tokens.MOVSLDUP(!pos,!pos));"movshdup" => (Tokens.MOVSHDUP(!pos,!pos));"haddps" => (Tokens.HADDPS(!pos,!pos));
"haddpd" => (Tokens.HADDPD(!pos,!pos));"hsubps" => (Tokens.HSUBPS(!pos,!pos));"hsubpd" => (Tokens.HSUBPD(!pos,!pos));
"lddqu" => (Tokens.LDDQU(!pos,!pos));

"psignb" => (Tokens.PSIGNB(!pos,!pos));"psignw" => (Tokens.PSIGNW(!pos,!pos));"psignd" => (Tokens.PSIGND(!pos,!pos));
"pshufb" => (Tokens.PSHUFB(!pos,!pos));"pmulhrsw" => (Tokens.PMULHRSW(!pos,!pos));"pmaddubsw" => (Tokens.PMADDUBSW(!pos,!pos));
"phsubw" => (Tokens.PHSUBW(!pos,!pos));"phsubsw" => (Tokens.PHSUBSW(!pos,!pos));"phsubd" => (Tokens.PHSUBD(!pos,!pos));
"phaddsw" => (Tokens.PHADDSW(!pos,!pos));"phaddw" => (Tokens.PHADDW(!pos,!pos));"phaddd" => (Tokens.PHADDD(!pos,!pos));
"palignr" => (Tokens.PALIGNR(!pos,!pos));"pabsb" => (Tokens.PABSB(!pos,!pos));"pabsw" => (Tokens.PABSW(!pos,!pos));
"pabsd" => (Tokens.PABSD(!pos,!pos));

"dpps" => (Tokens.DPPS(!pos,!pos));"dppd" => (Tokens.DPPD(!pos,!pos));"blendps" => (Tokens.BLENDPS(!pos,!pos));
"blendvps" => (Tokens.BLENDVPS(!pos,!pos));"blendpd" => (Tokens.BLENDPD(!pos,!pos));"blendvpd" => (Tokens.BLENDVPD(!pos,!pos));
"roundps" => (Tokens.ROUNDPS(!pos,!pos));"roundss" => (Tokens.ROUNDSS(!pos,!pos));"roundpd" => (Tokens.ROUNDPD(!pos,!pos));
"roundsd" => (Tokens.ROUNDSD(!pos,!pos));"insertps" => (Tokens.INSERTPS(!pos,!pos));"extractps" => (Tokens.EXTRACTPS(!pos,!pos));
"mpsadbw" => (Tokens.MPSADBW(!pos,!pos));"phminposuw" => (Tokens.PHMINPOSUW(!pos,!pos));"pmulld" => (Tokens.PMULLD(!pos,!pos));
"pmuldq" => (Tokens.PMULDQ(!pos,!pos));"pblendvb" => (Tokens.PBLENDVB(!pos,!pos));"pblendw" => (Tokens.PBLENDW(!pos,!pos));
"pminsb" => (Tokens.PMINSB(!pos,!pos));"pminuw" => (Tokens.PMINUW(!pos,!pos));"pminsd" => (Tokens.PMINSD(!pos,!pos));
"pminud" => (Tokens.PMINUD(!pos,!pos));"pmaxsb" => (Tokens.PMAXSB(!pos,!pos));"pmaxuw" => (Tokens.PMAXUW(!pos,!pos));
"pmaxsd" => (Tokens.PMAXSD(!pos,!pos));"pmaxud" => (Tokens.PMAXUD(!pos,!pos));"pinsrb" => (Tokens.PINSRB(!pos,!pos));
"pinsrd" => (Tokens.PINSRD(!pos,!pos));"pinsrq" => (Tokens.PINSRQ(!pos,!pos));"pextrb" => (Tokens.PEXTRB(!pos,!pos));
"pextrd" => (Tokens.PEXTRD(!pos,!pos));"pextrq" => (Tokens.PEXTRQ(!pos,!pos));
"pmovsxbw" => (Tokens.PMOVSXBW(!pos,!pos));"pmovzxbw" => (Tokens.PMOVZXBW(!pos,!pos));"pmovsxbd" => (Tokens.PMOVSXBD(!pos,!pos));
"pmovzxbd" => (Tokens.PMOVZXBD(!pos,!pos));"pmovsxbq" => (Tokens.PMOVSXBQ(!pos,!pos));"pmovzxbq" => (Tokens.PMOVZXBQ(!pos,!pos));
"pmovsxwd" => (Tokens.PMOVSXWD(!pos,!pos));"pmovzxwd" => (Tokens.PMOVZXWD(!pos,!pos));"pmovsxwq" => (Tokens.PMOVSXWQ(!pos,!pos));
"pmovzxwq" => (Tokens.PMOVZXWQ(!pos,!pos));"pmovsxdq" => (Tokens.PMOVSXDQ(!pos,!pos));"pmovzxdq" => (Tokens.PMOVZXDQ(!pos,!pos));
"ptest" => (Tokens.PTEST(!pos,!pos));"pcmpeqq" => (Tokens.PCMPEQQ(!pos,!pos));"packusdw" => (Tokens.PACKUSDW(!pos,!pos));
"movntdqa" => (Tokens.MOVNTDQA(!pos,!pos));

"vmptrld" => (Tokens.VMPTRLD(!pos,!pos));"vmptrst" => (Tokens.VMPTRST(!pos,!pos));"vmclear" => (Tokens.VMCLEAR(!pos,!pos));
"vmread" => (Tokens.VMREAD(!pos,!pos));"vmwrite" => (Tokens.VMWRITE(!pos,!pos));"vmcall" => (Tokens.VMCALL(!pos,!pos));
"vmlaunch" => (Tokens.VMLAUNCH(!pos,!pos));"vmresume" => (Tokens.VMRESUME(!pos,!pos));"vmxoff" => (Tokens.VMXOFF(!pos,!pos));
"vmxon" => (Tokens.VMXON(!pos,!pos)); "vmfunc" => (Tokens.VMFUNC(!pos,!pos)); "invvpid" => (Tokens.INVVPID(!pos,!pos)); 
"invept" => (Tokens.INVEPT(!pos,!pos)); 

"crc32" => (Tokens.CRC32(!pos,!pos));"popcnt" => (Tokens.POPCNT(!pos,!pos));

"pcmpestri" => (Tokens.PCMPESTRI(!pos,!pos));"pcmpestrm" => (Tokens.PCMPESTRM(!pos,!pos));
"pcmpistri" => (Tokens.PCMPISTRI(!pos,!pos));"pcmpistrm" => (Tokens.PCMPISTRM(!pos,!pos));
"pcmpgtq" => (Tokens.PCMPGTQ(!pos,!pos));

"vsqrtps" => (Tokens.VSQRTPS(!pos,!pos));"vsqrtpd" => (Tokens.VSQRTPD(!pos,!pos));"vrsqrtps" => (Tokens.VRSQRTPS(!pos,!pos));
"vrcpps" => (Tokens.VRCPPS(!pos,!pos));"vaddps" => (Tokens.VADDPS(!pos,!pos));"vaddpd" => (Tokens.VADDPD(!pos,!pos));
"vsubps" => (Tokens.VSUBPS(!pos,!pos));"vsubpd" => (Tokens.VSUBPD(!pos,!pos));"vmulps" => (Tokens.VMULPS(!pos,!pos));
"vmulpd" => (Tokens.VMULPD(!pos,!pos));"vdivps" => (Tokens.VDIVPS(!pos,!pos));"vdivpd" => (Tokens.VDIVPD(!pos,!pos));
"vcvtps2pd" => (Tokens.VCVTPS2PD(!pos,!pos));"vcvtpd2ps" => (Tokens.VCVTPD2PS(!pos,!pos));
"vcvtdq2ps" => (Tokens.VCVTDQ2PS(!pos,!pos));"vcvtps2dq" => (Tokens.VCVTPS2DQ(!pos,!pos));
"vcvttps2dq" => (Tokens.VCVTTPS2DQ(!pos,!pos));"vcvttpd2dq" => (Tokens.VCVTTPD2DQ(!pos,!pos));
"vcvtpd2dq" => (Tokens.VCVTPD2DQ(!pos,!pos));"vcvtdq2pd" => (Tokens.VCVTDQ2PD(!pos,!pos));"vminps" => (Tokens.VMINPS(!pos,!pos));
"vminpd" => (Tokens.VMINPD(!pos,!pos));"vmaxps" => (Tokens.VMAXPS(!pos,!pos));"vmaxpd" => (Tokens.VMAXPD(!pos,!pos));
"vhaddpd" => (Tokens.VHADDPD(!pos,!pos));"vhaddps" => (Tokens.VHADDPS(!pos,!pos));"vhsubpd" => (Tokens.VHSUBPD(!pos,!pos));
"vhsubps" => (Tokens.VHSUBPS(!pos,!pos));"vcmpps" => (Tokens.VCMPPS(!pos,!pos));"vcmppd" => (Tokens.VCMPPD(!pos,!pos));
"vaddsubpd" => (Tokens.VADDSUBPD(!pos,!pos));"vaddsubps" => (Tokens.VADDSUBPS(!pos,!pos));"vdpps" => (Tokens.VDPPS(!pos,!pos));
"vroundpd" => (Tokens.VROUNDPD(!pos,!pos));"vroundps" => (Tokens.VROUNDPS(!pos,!pos));"vmovaps" => (Tokens.VMOVAPS(!pos,!pos));
"vmovapd" => (Tokens.VMOVAPD(!pos,!pos));"vmovdqa" => (Tokens.VMOVDQA(!pos,!pos));"vmovups" => (Tokens.VMOVUPS(!pos,!pos));
"vmovupd" => (Tokens.VMOVUPD(!pos,!pos));"vmovdqu" => (Tokens.VMOVDQU(!pos,!pos));"vmovmskps" => (Tokens.VMOVMSKPS(!pos,!pos));
"vmovmskpd" => (Tokens.VMOVMSKPD(!pos,!pos));"vlddqu" => (Tokens.VLDDQU(!pos,!pos));"vmovntps" => (Tokens.VMOVNTPS(!pos,!pos));
"vmovntpd" => (Tokens.VMOVNTPD(!pos,!pos));"vmovntdq" => (Tokens.VMOVNTDQ(!pos,!pos));"vmovntdqa" => (Tokens.VMOVNTDQA(!pos,!pos));
"vmovshdup" => (Tokens.VMOVSHDUP(!pos,!pos));"vmovsldup" => (Tokens.VMOVSLDUP(!pos,!pos));"vmovddup" => (Tokens.VMOVDDUP(!pos,!pos));
"vunpckhpd" => (Tokens.VUNPCKHPD(!pos,!pos));"vunpckhps" => (Tokens.VUNPCKHPS(!pos,!pos));
"vunpcklpd" => (Tokens.VUNPCKLPD(!pos,!pos));"vblendps" => (Tokens.VBLENDPS(!pos,!pos));
"vblendpd" => (Tokens.VBLENDPD(!pos,!pos));"vshufpd" => (Tokens.VSHUFPD(!pos,!pos));"vshufps" => (Tokens.VSHUFPS(!pos,!pos));
"vunpcklps" => (Tokens.VUNPCKLPS(!pos,!pos));"vblendvps" => (Tokens.VBLENDVPS(!pos,!pos));
"vblendvpd" => (Tokens.VBLENDVPD(!pos,!pos));"vptest" => (Tokens.VPTEST(!pos,!pos));"vxorps" => (Tokens.VXORPS(!pos,!pos));
"vxorpd" => (Tokens.VXORPD(!pos,!pos));"vorps" => (Tokens.VORPS(!pos,!pos));"vorpd" => (Tokens.VORPD(!pos,!pos));
"vandnpd" => (Tokens.VANDNPD(!pos,!pos));"vandnps" => (Tokens.VANDNPS(!pos,!pos));"vandpd" => (Tokens.VANDPD(!pos,!pos));
"vandps" => (Tokens.VANDPS(!pos,!pos));"vbroadcastf128" => (Tokens.VBROADCASTF128(!pos,!pos));
"vbroadcastsd" => (Tokens.VBROADCASTSD(!pos,!pos));"vbroadcastss" => (Tokens.VBROADCASTSS(!pos,!pos));
"vextractf128" => (Tokens.VEXTRACTF128(!pos,!pos));"vinsertf128" => (Tokens.VINSERTF128(!pos,!pos));
"vmaskmovps" => (Tokens.VMASKMOVPS(!pos,!pos));"vmaskmovpd" => (Tokens.VMASKMOVPD(!pos,!pos));
"vpermilpd" => (Tokens.VPERMILPD(!pos,!pos));"vpermilps" => (Tokens.VPERMILPS(!pos,!pos));
"vperm2f128" => (Tokens.VPERM2F128(!pos,!pos));"vtestps" => (Tokens.VTESTPS(!pos,!pos));"vtestpd" => (Tokens.VTESTPD(!pos,!pos));
"vzeroall" => (Tokens.VZEROALL(!pos,!pos));"vzeroupper" => (Tokens.VZEROUPPER(!pos,!pos));
"vcvtsi2ss" => (Tokens.VCVTSI2SS(!pos,!pos));"vcvtsi2sd" => (Tokens.VCVTSI2SD(!pos,!pos));
"vcvtsd2si" => (Tokens.VCVTSD2SI(!pos,!pos));"vcvttss2si" => (Tokens.VCVTTSS2SI(!pos,!pos));
"vcvttsd2si" => (Tokens.VCVTTSD2SI(!pos,!pos));"vcvtss2si" => (Tokens.VCVTSS2SI(!pos,!pos));
"vcomisd" => (Tokens.VCOMISD(!pos,!pos));"vrsqrtss" => (Tokens.VRSQRTSS(!pos,!pos));"vrcpss" => (Tokens.VRCPSS(!pos,!pos));
"vucomiss" => (Tokens.VUCOMISS(!pos,!pos));"vucomisd" => (Tokens.VUCOMISD(!pos,!pos));"vcomiss" => (Tokens.VCOMISS(!pos,!pos));
"vaddss" => (Tokens.VADDSS(!pos,!pos));"vaddsd" => (Tokens.VADDSD(!pos,!pos));"vsubss" => (Tokens.VSUBSS(!pos,!pos));
"vsubsd" => (Tokens.VSUBSD(!pos,!pos));"vmulss" => (Tokens.VMULSS(!pos,!pos));"vmulsd" => (Tokens.VMULSD(!pos,!pos));
"vdivss" => (Tokens.VDIVSS(!pos,!pos));"vdivsd" => (Tokens.VDIVSD(!pos,!pos));"vsqrtss" => (Tokens.VSQRTSS(!pos,!pos));
"vsqrtsd" => (Tokens.VSQRTSD(!pos,!pos));"vcvtss2sd" => (Tokens.VCVTSS2SD(!pos,!pos));"vcvtsd2ss" => (Tokens.VCVTSD2SS(!pos,!pos));
"vminss" => (Tokens.VMINSS(!pos,!pos));"vminsd" => (Tokens.VMINSD(!pos,!pos));"vmaxss" => (Tokens.VMAXSS(!pos,!pos));
"vmaxsd" => (Tokens.VMAXSD(!pos,!pos));"vpand" => (Tokens.VPAND(!pos,!pos));"vpandn" => (Tokens.VPANDN(!pos,!pos));
"vpor" => (Tokens.VPOR(!pos,!pos));"vpxor" => (Tokens.VPXOR(!pos,!pos));"vpcmpgtb" => (Tokens.VPCMPGTB(!pos,!pos));
"vpcmpgtw" => (Tokens.VPCMPGTW(!pos,!pos));"vpcmpgtd" => (Tokens.VPCMPGTD(!pos,!pos));"vpmaddwd" => (Tokens.VPMADDWD(!pos,!pos));
"vpmaddubsw" => (Tokens.VPMADDUBSW(!pos,!pos));"vpavgb" => (Tokens.VPAVGB(!pos,!pos));"vpavgw" => (Tokens.VPAVGW(!pos,!pos));
"vpmuludq" => (Tokens.VPMULUDQ(!pos,!pos));"vpcmpeqb" => (Tokens.VPCMPEQB(!pos,!pos));"vpcmpeqw" => (Tokens.VPCMPEQW(!pos,!pos));
"vpcmpeqd" => (Tokens.VPCMPEQD(!pos,!pos));"vpmullw" => (Tokens.VPMULLW(!pos,!pos));"vpmulhuw" => (Tokens.VPMULHUW(!pos,!pos));
"vpmulhw" => (Tokens.VPMULHW(!pos,!pos));"vpsubsw" => (Tokens.VPSUBSW(!pos,!pos));

"vpaddsw" => (Tokens.VPADDSW(!pos,!pos));"vpsadbw" => (Tokens.VPSADBW(!pos,!pos));"vpaddusb" => (Tokens.VPADDUSB(!pos,!pos));
"vpaddusw" => (Tokens.VPADDUSW(!pos,!pos));"vpaddsb" => (Tokens.VPADDSB(!pos,!pos));"vpsubusb" => (Tokens.VPSUBUSB(!pos,!pos));
"vpsubusw" => (Tokens.VPSUBUSW(!pos,!pos));"vpsubsb" => (Tokens.VPSUBSB(!pos,!pos));"vpminub" => (Tokens.VPMINUB(!pos,!pos));
"vpminsw" => (Tokens.VPMINSW(!pos,!pos));"vpmaxub" => (Tokens.VPMAXUB(!pos,!pos));"vpmaxsw" => (Tokens.VPMAXSW(!pos,!pos));
"vpaddb" => (Tokens.VPADDB(!pos,!pos));"vpaddw" => (Tokens.VPADDW(!pos,!pos));"vpaddd" => (Tokens.VPADDD(!pos,!pos));
"vpaddq" => (Tokens.VPADDQ(!pos,!pos));"vpsubb" => (Tokens.VPSUBB(!pos,!pos));"vpsubw" => (Tokens.VPSUBW(!pos,!pos));
"vpsubd" => (Tokens.VPSUBD(!pos,!pos));"vpsubq" => (Tokens.VPSUBQ(!pos,!pos));"vpsllw" => (Tokens.VPSLLW(!pos,!pos));
"vpslld" => (Tokens.VPSLLD(!pos,!pos));"vpsllq" => (Tokens.VPSLLQ(!pos,!pos));"vpsraw" => (Tokens.VPSRAW(!pos,!pos));
"vpsrlw" => (Tokens.VPSRLW(!pos,!pos));"vpsrld" => (Tokens.VPSRLD(!pos,!pos));"vpsrlq" => (Tokens.VPSRLQ(!pos,!pos));
"vpsrad" => (Tokens.VPSRAD(!pos,!pos));"vphsubw" => (Tokens.VPHSUBW(!pos,!pos));"vphsubd" => (Tokens.VPHSUBD(!pos,!pos));
"vphsubsw" => (Tokens.VPHSUBSW(!pos,!pos));"vphaddw" => (Tokens.VPHADDW(!pos,!pos));"vphaddd" => (Tokens.VPHADDD(!pos,!pos));
"vphaddsw" => (Tokens.VPHADDSW(!pos,!pos));"vpmulhrsw" => (Tokens.VPMULHRSW(!pos,!pos));"vpsignb" => (Tokens.VPSIGNB(!pos,!pos));
"vpsignw" => (Tokens.VPSIGNW(!pos,!pos));"vpsignd" => (Tokens.VPSIGND(!pos,!pos));"vpabsb" => (Tokens.VPABSB(!pos,!pos));
"vpabsw" => (Tokens.VPABSW(!pos,!pos));"vpabsd" => (Tokens.VPABSD(!pos,!pos));"vdppd" => (Tokens.VDPPD(!pos,!pos));
"vphminposuw" => (Tokens.VPHMINPOSUW(!pos,!pos));"vmpsadbw" => (Tokens.VMPSADBW(!pos,!pos));"vpmaxsb" => (Tokens.VPMAXSB(!pos,!pos));
"vpmaxsd" => (Tokens.VPMAXSD(!pos,!pos));"vpmaxud" => (Tokens.VPMAXUD(!pos,!pos));"vpminsb" => (Tokens.VPMINSB(!pos,!pos));
"vpminsd" => (Tokens.VPMINSD(!pos,!pos));"vpminud" => (Tokens.VPMINUD(!pos,!pos));"vpmaxuw" => (Tokens.VPMAXUW(!pos,!pos));
"vpminuw" => (Tokens.VPMINUW(!pos,!pos));"vpmovsxbw" => (Tokens.VPMOVSXBW(!pos,!pos));"vpmovzxbw" => (Tokens.VPMOVZXBW(!pos,!pos));
"vpmovsxbd" => (Tokens.VPMOVSXBD(!pos,!pos));"vpmovzxbd" => (Tokens.VPMOVZXBD(!pos,!pos));"vpmovsxbq" => (Tokens.VPMOVSXBQ(!pos,!pos));
"vpmovzxbq" => (Tokens.VPMOVZXBQ(!pos,!pos));"vpmovsxwd" => (Tokens.VPMOVSXWD(!pos,!pos));"vpmovzxwd" => (Tokens.VPMOVZXWD(!pos,!pos));
"vpmovsxwq" => (Tokens.VPMOVSXWQ(!pos,!pos));"vpmovzxwq" => (Tokens.VPMOVZXWQ(!pos,!pos));"vpmovsxdq" => (Tokens.VPMOVSXDQ(!pos,!pos));
"vpmovzxdq" => (Tokens.VPMOVZXDQ(!pos,!pos));"vpmuldq" => (Tokens.VPMULDQ(!pos,!pos));"vpmulld" => (Tokens.VPMULLD(!pos,!pos));
"vroundsd" => (Tokens.VROUNDSD(!pos,!pos));"vroundss" => (Tokens.VROUNDSS(!pos,!pos));"vpopcnt" => (Tokens.VPOPCNT(!pos,!pos));
"vpcmpgtq" => (Tokens.VPCMPGTQ(!pos,!pos));"vpcmpestri" => (Tokens.VPCMPESTRI(!pos,!pos));"vpcmpestrm" => (Tokens.VPCMPESTRM(!pos,!pos));
"vpcmpistri" => (Tokens.VPCMPISTRI(!pos,!pos));"vpcmpistrm" => (Tokens.VPCMPISTRM(!pos,!pos));
"vpclmulqdq" => (Tokens.VPCLMULQDQ(!pos,!pos));"vaesdec" => (Tokens.VAESDEC(!pos,!pos));
"vaesdeclast" => (Tokens.VAESDECLAST(!pos,!pos));"vaesenc" => (Tokens.VAESENC(!pos,!pos));
"vaesenclast" => (Tokens.VAESENCLAST(!pos,!pos));"vaesimx" => (Tokens.VAESIMX(!pos,!pos));
"vaeskeygenassist" => (Tokens.VAESKEYGENASSIST(!pos,!pos));
"vstmxcsr" => (Tokens.VSTMXCSR(!pos,!pos));"vmovss" => (Tokens.VMOVSS(!pos,!pos));"vmovsd" => (Tokens.VMOVSD(!pos,!pos));
"vcmpss" => (Tokens.VCMPSS(!pos,!pos));"vcmpsd" => (Tokens.VCMPSD(!pos,!pos));"vmovhps" => (Tokens.VMOVHPS(!pos,!pos));
"vmovhpd" => (Tokens.VMOVHPD(!pos,!pos));"vmovlps" => (Tokens.VMOVLPS(!pos,!pos));"vmovlpd" => (Tokens.VMOVLPD(!pos,!pos));
"vmovlhps" => (Tokens.VMOVLHPS(!pos,!pos));"vmovhlps" => (Tokens.VMOVHLPS(!pos,!pos));"vmovq" => (Tokens.VMOVQ(!pos,!pos));
"vmovd" => (Tokens.VMOVD(!pos,!pos));"vpackuswb" => (Tokens.VPACKUSWB(!pos,!pos));"vpackssdw" => (Tokens.VPACKSSDW(!pos,!pos));
"vpacksswb" => (Tokens.VPACKSSWB(!pos,!pos));"vpunpckhbw" => (Tokens.VPUNPCKHBW(!pos,!pos));
"vpunpckhwd" => (Tokens.VPUNPCKHWD(!pos,!pos));"vpunpcklbw" => (Tokens.VPUNPCKLBW(!pos,!pos));
"vpunpcklwd" => (Tokens.VPUNPCKLWD(!pos,!pos));"vpunpckhdq" => (Tokens.VPUNPCKHDQ(!pos,!pos));
"vpunpckldq" => (Tokens.VPUNPCKLDQ(!pos,!pos));"vpunpcklqdq" => (Tokens.VPUNPCKLQDQ(!pos,!pos));
"vpunpckhqdq" => (Tokens.VPUNPCKHQDQ(!pos,!pos));"vpshufhw" => (Tokens.VPSHUFHW(!pos,!pos));
"vpshuflw" => (Tokens.VPSHUFLW(!pos,!pos));"vpshufd" => (Tokens.VPSHUFD(!pos,!pos));"vpmovmskb" => (Tokens.VPMOVMSKB(!pos,!pos));
"vmaskmovdqu" => (Tokens.VMASKMOVDQU(!pos,!pos));"vpinsrw" => (Tokens.VPINSRW(!pos,!pos));"vpextrw" => (Tokens.VPEXTRW(!pos,!pos));
"vpalignr" => (Tokens.VPALIGNR(!pos,!pos));"vpshufb" => (Tokens.VPSHUFB(!pos,!pos));"vextractps" => (Tokens.VEXTRACTPS(!pos,!pos));
"vinsertps" => (Tokens.VINSERTPS(!pos,!pos));"vpackusdw" => (Tokens.VPACKUSDW(!pos,!pos));"vpcmpeqq" => (Tokens.VPCMPEQQ(!pos,!pos));
"vpblendvb" => (Tokens.VPBLENDVB(!pos,!pos));"vpblendw" => (Tokens.VPBLENDW(!pos,!pos));"vpextrb" => (Tokens.VPEXTRB(!pos,!pos));
"vpextrd" => (Tokens.VPEXTRD(!pos,!pos));"vpextrq" => (Tokens.VPEXTRQ(!pos,!pos));"vpinsrb" => (Tokens.VPINSRB(!pos,!pos));
"vpinsrd" => (Tokens.VPINSRD(!pos,!pos));"vpinsrq" => (Tokens.VPINSRQ(!pos,!pos));

"vfmadd132pd" => (Tokens.VFMADD132PD(!pos,!pos));"vfmadd213pd" => (Tokens.VFMADD213PD(!pos,!pos));
"vfmadd231pd" => (Tokens.VFMADD231PD(!pos,!pos));"vfmadd132ps" => (Tokens.VFMADD132PS(!pos,!pos));
"vfmadd213ps" => (Tokens.VFMADD213PS(!pos,!pos));"vfmadd231ps" => (Tokens.VFMADD231PS(!pos,!pos));
"vfmadd132sd" => (Tokens.VFMADD132SD(!pos,!pos));"vfmadd213sd" => (Tokens.VFMADD213SD(!pos,!pos));
"vfmadd231sd" => (Tokens.VFMADD231SD(!pos,!pos));"vfmadd132ss" => (Tokens.VFMADD132SS(!pos,!pos));
"vfmadd213ss" => (Tokens.VFMADD213SS(!pos,!pos));"vfmadd231ss" => (Tokens.VFMADD231SS(!pos,!pos));
"vfmaddsub132pd" => (Tokens.VFMADDSUB132PD(!pos,!pos));"vfmaddsub213pd" => (Tokens.VFMADDSUB213PD(!pos,!pos));
"vfmaddsub231pd" => (Tokens.VFMADDSUB231PD(!pos,!pos));"vfmaddsub132ps" => (Tokens.VFMADDSUB132PS(!pos,!pos));
"vfmaddsub213ps" => (Tokens.VFMADDSUB213PS(!pos,!pos));"vfmaddsub231ps" => (Tokens.VFMADDSUB231PS(!pos,!pos));
"vfmsubadd132pd" => (Tokens.VFMSUBADD132PD(!pos,!pos));"vfmsubadd213pd" => (Tokens.VFMSUBADD213PD(!pos,!pos));
"vfmsubadd231pd" => (Tokens.VFMSUBADD231PD(!pos,!pos));"vfmsubadd132ps" => (Tokens.VFMSUBADD132PS(!pos,!pos));
"vfmsubadd213ps" => (Tokens.VFMSUBADD213PS(!pos,!pos));"vfmsubadd231ps" => (Tokens.VFMSUBADD231PS(!pos,!pos));
"vfmsub132pd" => (Tokens.VFMSUB132PD(!pos,!pos));"vfmsub213pd" => (Tokens.VFMSUB213PD(!pos,!pos));
"vfmsub231pd" => (Tokens.VFMSUB231PD(!pos,!pos));"vfmsub132ps" => (Tokens.VFMSUB132PS(!pos,!pos));
"vfmsub213ps" => (Tokens.VFMSUB213PS(!pos,!pos));"vfmsub231ps" => (Tokens.VFMSUB231PS(!pos,!pos));
"vfmsub132sd" => (Tokens.VFMSUB132SD(!pos,!pos));"vfmsub213sd" => (Tokens.VFMSUB213SD(!pos,!pos));
"vfmsub231sd" => (Tokens.VFMSUB231SD(!pos,!pos));"vfmsub132ss" => (Tokens.VFMSUB132SS(!pos,!pos));
"vfmsub213ss" => (Tokens.VFMSUB213SS(!pos,!pos));"vfmsub231ss" => (Tokens.VFMSUB231SS(!pos,!pos));
"vfnmadd132pd" => (Tokens.VFNMADD132PD(!pos,!pos));"vfnmadd213pd" => (Tokens.VFNMADD213PD(!pos,!pos));
"vfnmadd231pd" => (Tokens.VFNMADD231PD(!pos,!pos));"vfnmadd132ps" => (Tokens.VFNMADD132PS(!pos,!pos));
"vfnmadd213ps" => (Tokens.VFNMADD213PS(!pos,!pos));"vfnmadd231ps" => (Tokens.VFNMADD231PS(!pos,!pos));
"vfnmadd132sd" => (Tokens.VFNMADD132SD(!pos,!pos));"vfnmadd213sd" => (Tokens.VFNMADD213SD(!pos,!pos));
"vfnmadd231sd" => (Tokens.VFNMADD231SD(!pos,!pos));"vfnmadd132ss" => (Tokens.VFNMADD132SS(!pos,!pos));
"vfnmadd213ss" => (Tokens.VFNMADD213SS(!pos,!pos));"vfnmadd231ss" => (Tokens.VFNMADD231SS(!pos,!pos));
"vfnmsub132pd" => (Tokens.VFNMSUB132PD(!pos,!pos));"vfnmsub213pd" => (Tokens.VFNMSUB213PD(!pos,!pos));
"vfnmsub231pd" => (Tokens.VFNMSUB231PD(!pos,!pos));"vfnmsub132ps" => (Tokens.VFNMSUB132PS(!pos,!pos));
"vfnmsub213ps" => (Tokens.VFNMSUB213PS(!pos,!pos));"vfnmsub231ps" => (Tokens.VFNMSUB231PS(!pos,!pos));
"vfnmsub132sd" => (Tokens.VFNMSUB132SD(!pos,!pos));"vfnmsub213sd" => (Tokens.VFNMSUB213SD(!pos,!pos));
"vfnmsub231sd" => (Tokens.VFNMSUB231SD(!pos,!pos));"vfnmsub132ss" => (Tokens.VFNMSUB132SS(!pos,!pos));
"vfnmsub213ss" => (Tokens.VFNMSUB213SS(!pos,!pos));"vfnmsub231ss" => (Tokens.VFNMSUB231SS(!pos,!pos));

"andn" => (Tokens.ANDN(!pos,!pos));"bextr" => (Tokens.BEXTR(!pos,!pos));"blsi" => (Tokens.BLSI(!pos,!pos));
"blsmsk" => (Tokens.BLSMSK(!pos,!pos));"blsr" => (Tokens.BLSR(!pos,!pos));"bzhi" => (Tokens.BZHI(!pos,!pos));
"lzcnt" => (Tokens.LZCNT(!pos,!pos));"mulx" => (Tokens.MULX(!pos,!pos));"pdep" => (Tokens.PDEP(!pos,!pos));
"pext" => (Tokens.PEXT(!pos,!pos));"rorx" => (Tokens.RORX(!pos,!pos));"sarx" => (Tokens.SARX(!pos,!pos));
"shlx" => (Tokens.SHLX(!pos,!pos));"shrx" => (Tokens.SHRX(!pos,!pos));"tzcnt" => (Tokens.TZCNT(!pos,!pos));

"vpbroadcastb" => (Tokens.VPBROADCASTB(!pos,!pos));"vpbroadcastd" => (Tokens.VPBROADCASTD(!pos,!pos));
"vpbroadcastq" => (Tokens.VPBROADCASTQ(!pos,!pos));"vpbroadcastw" => (Tokens.VPBROADCASTW(!pos,!pos));

"#"						=> (Tokens.HASHY(!pos,!pos));
"CODESEGMENT" => (Tokens.CODESEGMENT(!pos,!pos));
"DATASEGMENT" => (Tokens.DATASEGMENT(!pos,!pos));
"xgetbv" => (Tokens.XGETBV(!pos,!pos));
"lock" => (Tokens.LOCK(!pos,!pos));
"data16" => (Tokens.DATA16(!pos,!pos));

"XMMWORD PTR"				=> (Tokens.XMMWORDPTR(!pos,!pos)); 
"QWORD PTR"				=> (Tokens.QWORDPTR(!pos,!pos)); 
"DWORD PTR"				=> (Tokens.DWORDPTR(!pos,!pos)); 
"BYTE PTR"				=> (Tokens.BYTEPTR(!pos,!pos)); 
"WORD PTR"				=> (Tokens.WORDPTR(!pos,!pos)); 

"zmm0"=>(Tokens.ZMM0(!pos,!pos));"zmm1"=>(Tokens.ZMM1(!pos,!pos));"zmm2"=>(Tokens.ZMM2(!pos,!pos));"zmm3"=>(Tokens.ZMM3(!pos,!pos));
"zmm4"=>(Tokens.ZMM4(!pos,!pos));"zmm5"=>(Tokens.ZMM5(!pos,!pos));"zmm6"=>(Tokens.ZMM6(!pos,!pos));"zmm7"=>(Tokens.ZMM7(!pos,!pos));
"zmm8"=>(Tokens.ZMM8(!pos,!pos));"zmm9"=>(Tokens.ZMM9(!pos,!pos));"zmm10"=>(Tokens.ZMM10(!pos,!pos));"zmm11"=>(Tokens.ZMM11(!pos,!pos));
"zmm12"=>(Tokens.ZMM12(!pos,!pos));"zmm13"=>(Tokens.ZMM13(!pos,!pos));"zmm14"=>(Tokens.ZMM14(!pos,!pos));"zmm15"=>(Tokens.ZMM15(!pos,!pos));
"zmm16"=>(Tokens.ZMM16(!pos,!pos));"zmm17"=>(Tokens.ZMM17(!pos,!pos));"zmm18"=>(Tokens.ZMM18(!pos,!pos));"zmm19"=>(Tokens.ZMM19(!pos,!pos));
"zmm20"=>(Tokens.ZMM20(!pos,!pos));"zmm21"=>(Tokens.ZMM21(!pos,!pos));"zmm22"=>(Tokens.ZMM22(!pos,!pos));"zmm23"=>(Tokens.ZMM23(!pos,!pos));
"zmm24"=>(Tokens.ZMM24(!pos,!pos));"zmm25"=>(Tokens.ZMM25(!pos,!pos));"zmm26"=>(Tokens.ZMM26(!pos,!pos));"zmm27"=>(Tokens.ZMM27(!pos,!pos)); 
"zmm28"=>(Tokens.ZMM28(!pos,!pos));"zmm29"=>(Tokens.ZMM29(!pos,!pos));"zmm30"=>(Tokens.ZMM30(!pos,!pos));"zmm31"=>(Tokens.ZMM31(!pos,!pos)); 

"ymm0"=>(Tokens.YMM0(!pos,!pos));"ymm1"=>(Tokens.YMM1(!pos,!pos));"ymm2"=>(Tokens.YMM2(!pos,!pos));"ymm3"=>(Tokens.YMM3(!pos,!pos));
"ymm4"=>(Tokens.YMM4(!pos,!pos));"ymm5"=>(Tokens.YMM5(!pos,!pos));"ymm6"=>(Tokens.YMM6(!pos,!pos));"ymm7"=>(Tokens.YMM7(!pos,!pos));
"ymm8"=>(Tokens.YMM8(!pos,!pos));"ymm9"=>(Tokens.YMM9(!pos,!pos));"ymm10"=>(Tokens.YMM10(!pos,!pos));"ymm11"=>(Tokens.YMM11(!pos,!pos));
"ymm12"=>(Tokens.YMM12(!pos,!pos));"ymm13"=>(Tokens.YMM13(!pos,!pos));"ymm14"=>(Tokens.YMM14(!pos,!pos));"ymm15"=>(Tokens.YMM15(!pos,!pos));
"ymm16"=>(Tokens.YMM16(!pos,!pos));"ymm17"=>(Tokens.YMM17(!pos,!pos));"ymm18"=>(Tokens.YMM18(!pos,!pos));"ymm19"=>(Tokens.YMM19(!pos,!pos));
"ymm20"=>(Tokens.YMM20(!pos,!pos));"ymm21"=>(Tokens.YMM21(!pos,!pos));"ymm22"=>(Tokens.YMM22(!pos,!pos));"ymm23"=>(Tokens.YMM23(!pos,!pos));
"ymm24"=>(Tokens.YMM24(!pos,!pos));"ymm25"=>(Tokens.YMM25(!pos,!pos));"ymm26"=>(Tokens.YMM26(!pos,!pos));"ymm27"=>(Tokens.YMM27(!pos,!pos)); 
"ymm28"=>(Tokens.YMM28(!pos,!pos));"ymm29"=>(Tokens.YMM29(!pos,!pos));"ymm30"=>(Tokens.YMM30(!pos,!pos));"ymm31"=>(Tokens.YMM31(!pos,!pos)); 

"xmm0"=>(Tokens.XMM0(!pos,!pos));"xmm1"=>(Tokens.XMM1(!pos,!pos));"xmm2"=>(Tokens.XMM2(!pos,!pos));"xmm3"=>(Tokens.XMM3(!pos,!pos));
"xmm4"=>(Tokens.XMM4(!pos,!pos));"xmm5"=>(Tokens.XMM5(!pos,!pos));"xmm6"=>(Tokens.XMM6(!pos,!pos));"xmm7"=>(Tokens.XMM7(!pos,!pos));
"xmm8"=>(Tokens.XMM8(!pos,!pos));"xmm9"=>(Tokens.XMM9(!pos,!pos));"xmm10"=>(Tokens.XMM10(!pos,!pos));"xmm11"=>(Tokens.XMM11(!pos,!pos));
"xmm12"=>(Tokens.XMM12(!pos,!pos));"xmm13"=>(Tokens.XMM13(!pos,!pos));"xmm14"=>(Tokens.XMM14(!pos,!pos));"xmm15"=>(Tokens.XMM15(!pos,!pos));
"xmm16"=>(Tokens.XMM16(!pos,!pos));"xmm17"=>(Tokens.XMM17(!pos,!pos));"xmm18"=>(Tokens.XMM18(!pos,!pos));"xmm19"=>(Tokens.XMM19(!pos,!pos));
"xmm20"=>(Tokens.XMM20(!pos,!pos));"xmm21"=>(Tokens.XMM21(!pos,!pos));"xmm22"=>(Tokens.XMM22(!pos,!pos));"xmm23"=>(Tokens.XMM23(!pos,!pos));
"xmm24"=>(Tokens.XMM24(!pos,!pos));"xmm25"=>(Tokens.XMM25(!pos,!pos));"xmm26"=>(Tokens.XMM26(!pos,!pos));"xmm27"=>(Tokens.XMM27(!pos,!pos)); 
"xmm28"=>(Tokens.XMM28(!pos,!pos));"xmm29"=>(Tokens.XMM29(!pos,!pos));"xmm30"=>(Tokens.XMM30(!pos,!pos));"xmm31"=>(Tokens.XMM31(!pos,!pos)); 

"rax"=>(Tokens.RAX(!pos,!pos));"rbx"=>(Tokens.RBX(!pos,!pos));"rcx"=>(Tokens.RCX(!pos,!pos));"rdx"=>(Tokens.RDX(!pos,!pos));
"rbp"=>(Tokens.RBP(!pos,!pos));"rsp"=>(Tokens.RSP(!pos,!pos));"rsi"=>(Tokens.RSI(!pos,!pos));"rdi"=>(Tokens.RDI(!pos,!pos)); 
"rip"=>(Tokens.RIP(!pos,!pos)); 
"r8"=>(Tokens.R8(!pos,!pos));"r9"=>(Tokens.R9(!pos,!pos));"r10"=>(Tokens.R10(!pos,!pos));"r11"=>(Tokens.R11(!pos,!pos)); 
"r12"=>(Tokens.R12(!pos,!pos));"r13"=>(Tokens.R13(!pos,!pos));"r14"=>(Tokens.R14(!pos,!pos));"r15"=>(Tokens.R15(!pos,!pos)); 
"cs"=>(Tokens.CS(!pos,!pos));"ds"=>(Tokens.DS(!pos,!pos));"es"=>(Tokens.ES(!pos,!pos));"fs"=>(Tokens.FS(!pos,!pos));"gs"=>(Tokens.GS(!pos,!pos));"ss"=>(Tokens.SS(!pos,!pos)); 

"eax"=>(Tokens.EAX(!pos,!pos));"ebx"=>(Tokens.EBX(!pos,!pos));"ecx"=>(Tokens.ECX(!pos,!pos));"edx"=>(Tokens.EDX(!pos,!pos));
"ebp"=>(Tokens.EBP(!pos,!pos));"esp"=>(Tokens.ESP(!pos,!pos));"esi"=>(Tokens.ESI(!pos,!pos));"edi"=>(Tokens.EDI(!pos,!pos)); 
"r8d"=>(Tokens.R8D(!pos,!pos));"r9d"=>(Tokens.R9D(!pos,!pos));"r10d"=>(Tokens.R10D(!pos,!pos));"r11d"=>(Tokens.R11D(!pos,!pos)); 
"r12d"=>(Tokens.R12D(!pos,!pos));"r13d"=>(Tokens.R13D(!pos,!pos));"r14d"=>(Tokens.R14D(!pos,!pos));"r15d"=>(Tokens.R15D(!pos,!pos)); 
 
"ax"=>(Tokens.AX(!pos,!pos));"bx"=>(Tokens.BX(!pos,!pos));"cx"=>(Tokens.CX(!pos,!pos));"dx"=>(Tokens.DX(!pos,!pos));
"bp"=>(Tokens.BP(!pos,!pos));"sp"=>(Tokens.SP(!pos,!pos));"si"=>(Tokens.SI(!pos,!pos));"di"=>(Tokens.DI(!pos,!pos)); 
"r8w"=>(Tokens.R8W(!pos,!pos));"r9w"=>(Tokens.R9W(!pos,!pos));"r10w"=>(Tokens.R10W(!pos,!pos));"r11w"=>(Tokens.R11W(!pos,!pos)); 
"r12w"=>(Tokens.R12W(!pos,!pos));"r13w"=>(Tokens.R13W(!pos,!pos));"r14w"=>(Tokens.R14W(!pos,!pos));"r15w"=>(Tokens.R15W(!pos,!pos)); 
 
"ah"=>(Tokens.AH(!pos,!pos));"bh"=>(Tokens.BH(!pos,!pos));"ch"=>(Tokens.CH(!pos,!pos));"dh"=>(Tokens.DH(!pos,!pos));
"al"=>(Tokens.AL(!pos,!pos));"bl"=>(Tokens.BL(!pos,!pos));"cl"=>(Tokens.CL(!pos,!pos));"dl"=>(Tokens.DL(!pos,!pos));
"bpl"=>(Tokens.BPL(!pos,!pos));"spl"=>(Tokens.SPL(!pos,!pos));"sil"=>(Tokens.SIL(!pos,!pos));"dil"=>(Tokens.DIL(!pos,!pos)); 
"r8b"=>(Tokens.R8B(!pos,!pos));"r9b"=>(Tokens.R9B(!pos,!pos));"r10b"=>(Tokens.R10B(!pos,!pos));"r11b"=>(Tokens.R11B(!pos,!pos)); 
"r12b"=>(Tokens.R12B(!pos,!pos));"r13b"=>(Tokens.R13B(!pos,!pos));"r14b"=>(Tokens.R14B(!pos,!pos));"r15b"=>(Tokens.R15B(!pos,!pos)); 

L?\"(\\.|[^\\"])*\"  => (Tokens.QUOTESTRING((yytext, yyleng), !pos,!pos));
"."						=> (Tokens.DOT(!pos,!pos)); 
","						=> (Tokens.COMMA(!pos,!pos)); 
":"						=> (Tokens.COLON(!pos,!pos)); 
"["						=> (Tokens.LBRACKET(!pos,!pos)); 
"]"						=> (Tokens.RBRACKET(!pos,!pos)); 
"("						=> (Tokens.LPAR(!pos,!pos)); 
")"						=> (Tokens.RPAR(!pos,!pos)); 
"+"						=> (Tokens.PLUS(!pos,!pos)); 
"-"						=> (Tokens.MINUS(!pos,!pos)); 
"*"						=> (Tokens.MULT(!pos,!pos)); 
"0x"					=> (Tokens.HEXPREFIX((!pos,!pos))); 
\n						=> (pos := (!pos) + 1; inc linenum; Tokens.NEWLINE(!pos,!pos));
{ws}+					=> (lex());
[a-f0-9]+		=> (Tokens.NAT((hex_to_int yytext), !pos, !pos));
