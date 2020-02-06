(*

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 
 *)


val mk_int = HOLogic.mk_number @{typ int} 
val mk_nat = HOLogic.mk_number @{typ nat}
val mk_string = HOLogic.mk_string 
val mk_list = HOLogic.mk_list

val section_number = ref 0


datatype bit_mask = 
Eight | EightHigh | Sixteen | ThirtyTwo | SixtyFour | OneHundredTwentyEight | TwoHundredFiftySix | FiveHundredTwelve

fun mk_bit_mask i = 
              if i=8 then 
                          Const ("MachineDatatypes.bit_mask.Eight", @{typ "bit_mask"})    
              else if i=9 then 
                          Const ("MachineDatatypes.bit_mask.EightHigh", @{typ "bit_mask"})    
              else if i=16 then 
                          Const ("MachineDatatypes.bit_mask.Sixteen", @{typ "bit_mask"})
              else if i=32 then 
                          Const ("MachineDatatypes.bit_mask.ThirtyTwo", @{typ "bit_mask"})
              else if i=64 then
                          Const ("MachineDatatypes.bit_mask.SixtyFour", @{typ "bit_mask"})
              else if i=128 then
                          Const ("MachineDatatypes.bit_mask.OneHundredTwentyEight", @{typ "bit_mask"})
              else if i=256 then
                          Const ("MachineDatatypes.bit_mask.TwoHundredFiftySix", @{typ "bit_mask"})
              else 
                          Const ("MachineDatatypes.bit_mask.FiveHundredTwelve", @{typ "bit_mask"})

fun mk_register_mnemonic r =  Const ("MachineDatatypes.register_mnemonic."^r, @{typ "register_mnemonic"})
fun mk_register_mnemonic_128lower r =  Const ("MachineDatatypes.register_mnemonic."^r^"w0", @{typ "register_mnemonic"})
fun mk_register_mnemonic_128upper r =  Const ("MachineDatatypes.register_mnemonic."^r^"w1", @{typ "register_mnemonic"})
fun mk_register_mnemonic_256_1 r =  Const ("MachineDatatypes.register_mnemonic."^r^"w0", @{typ "register_mnemonic"})
fun mk_register_mnemonic_256_2 r =  Const ("MachineDatatypes.register_mnemonic."^r^"w1", @{typ "register_mnemonic"})
fun mk_register_mnemonic_256_3 r =  Const ("MachineDatatypes.register_mnemonic."^r^"w2", @{typ "register_mnemonic"})
fun mk_register_mnemonic_256_4 r =  Const ("MachineDatatypes.register_mnemonic."^r^"w3", @{typ "register_mnemonic"})

fun mk_register (i,r) =  
  if i < 128 then
    @{term "General"} $ mk_bit_mask i $ mk_register_mnemonic r 
  else 
    @{term "SIMD"} $ mk_bit_mask i $ mk_register_mnemonic_256_4 r  $ mk_register_mnemonic_256_3 r $ mk_register_mnemonic_256_2 r $ mk_register_mnemonic_256_1 r    

(* $ mk_register_mnemonic_128upper r $ mk_register_mnemonic_128lower r *)

fun mk_register_sig i =  
  if i < 128 then
    @{term "General_sig"} $ mk_bit_mask i 
  else 
    @{term "SIMD_sig"} $ mk_bit_mask i

fun toString_bit_mask i = 
              if i=8 then 
                "Eight"
              else if i=9 then 
                "EightHigh"    
              else if i=16 then 
                "Sixteen"
              else if i=32 then 
                "ThirtyTwo"
              else if i=64 then
                "SixtyFour"
              else if i=128 then
                "OneHundredTwentyEight"
              else if i=256 then
                "TwoHundredFiftySix"
              else
                "FiveHundredTwelve"

fun toString_register(i,r) = 
  if i < 128 then
    "General " ^ (toString_bit_mask i) ^ " " ^  r 
  else
    "SIMD " ^ (toString_bit_mask i) ^ " " ^  r

fun toString_register_sig i = 
  if i < 128 then
    "General " ^ (toString_bit_mask i)  
  else
    "SIMD " ^ (toString_bit_mask i)  
                                                                      
(* REGISTERS END *)

(* IMMEDIATE BEGIN *)

datatype immediate =                         
    ImmVal   of int 
  | ImmLabel of string


fun mk_immediate (ImmVal i) = @{term "ImmVal"} $ mk_int i
  | mk_immediate (ImmLabel s) = @{term "ImmLabel"} $ mk_string s

fun toString_immediate (ImmVal i) =  "ImmVal "^toString i
  | toString_immediate (ImmLabel l) =  "ImmLabel " ^l

(* IMMEDIATE END *)

(* MEMORY BEGIN *)
datatype address = 
    A_FromReg of (int * string)
  | A_Label of string
  | A_Constant of int
  | A_Plus of (address * address)
  | A_Minus of (address * address)
  | A_Mult of (int * address)

fun mk_address (A_FromReg (i, r)) = @{term "A_FromReg"} $ mk_register(i,r) 
  | mk_address (A_Label l) = @{term "A_Label"} $ mk_string l
  | mk_address (A_Constant c) = @{term "A_Constant"} $ mk_int c
  | mk_address (A_Plus (a0,a1)) = @{term "A_Plus"} $ mk_address a0 $ mk_address a1
  | mk_address (A_Minus (a0,a1)) = @{term "A_Minus"} $ mk_address a0 $ mk_address a1
  | mk_address (A_Mult (i,a)) = @{term "A_Mult"} $ mk_int i $ mk_address a

fun toString_address1 (A_FromReg (i, reg)) = "A_FromReg " ^ toString_bit_mask i ^ " " ^ reg
  | toString_address1 (A_Label label) = label
  | toString_address1 (A_Constant c) = toString c
  | toString_address1 (A_Plus (a0,a1)) = toString_address1 a0 ^ " + " ^ toString_address1 a1
  | toString_address1 (A_Minus (a0,a1)) = toString_address1 a0 ^ " - " ^ toString_address1 a1
  | toString_address1 (A_Mult (i,a)) = toString i ^ "*" ^ toString_address1 a

fun toString_address a = "[" ^ toString_address1 a ^ "]"

(* ADDRESS END  *)



(* OPERAND DEST BEGIN *)

datatype operand_dest =
    Reg of (int*string)
|    Memory of (int*address)

datatype operand_dest_sig =
    Reg_sig of int
  | Memory_sig of int

fun mk_operand_dest (Memory (i,a)) = @{term "Memory"} $  mk_bit_mask i $  mk_address a
  | mk_operand_dest (Reg (i,r)) = @{term "Reg"}   $ mk_register(i,r)   

fun mk_operand_dest_sig (Reg_sig i) = @{term "Reg_sig"}   $ mk_register_sig i   
  | mk_operand_dest_sig (Memory_sig i) = @{term "Memory_sig"} $ mk_bit_mask i


fun toString_operand_dest (Memory (i,a)) = "( Memory " ^ toString_bit_mask (i) ^ toString_address a ^ ")"
  | toString_operand_dest (Reg (i,r)) = "( Reg " ^ toString_register(i,r) ^ ")"

fun toString_operand_dest_sig (Reg_sig i) =  "( Reg_sig " ^ toString_register_sig i ^ ")"
  | toString_operand_dest_sig (Memory_sig i) = "( Memory_sig " ^ toString_bit_mask i ^ ")"

(* OPERAND DEST END *)


(* OPERAND SRC BEGIN *)

datatype operand_src =
    Storage of operand_dest
    |Immediate of (int*immediate)
datatype operand_src_sig =
    Storage_sig of operand_dest_sig
    |Immediate_sig


fun mk_operand_src (Storage s) = @{term "Storage"} $ mk_operand_dest s
  | mk_operand_src (Immediate (i,c)) = @{term "Immediate"} $ mk_bit_mask i $ mk_immediate c

fun toString_operand_src (Storage s) = "( Storage " ^ toString_operand_dest s ^ ")"
  | toString_operand_src (Immediate (i,c)) = "( Immediate " ^ toString_bit_mask i ^ " " ^ toString_immediate c ^ ")"


fun mk_operand_src_sig (Storage_sig s) = @{term "Storage_sig"} $ mk_operand_dest_sig s
  | mk_operand_src_sig (Immediate_sig) = @{term "Immediate_sig"} 

fun toString_operand_src_sig (Storage_sig s) = "(Storage_sig " ^ toString_operand_dest_sig s ^ ")"
  | toString_operand_src_sig (Immediate_sig) = "(Immediate_sig)"

(* OPERAND SRC END *)

datatype instr_mnemonic_8088 =
    Aaa | Aad | Aam | Aas | Adc | Add | And | Call | Cbw | Clc | 
    Cld | Cli | Cmc | Cmp | Cmpsb | Cwd | Daa | Das | Dec | Div | 
    Esc | Hlt | Idiv | Imul | In | Inc | INS_Int | Into | Iret | Ja | 
    Jae | Jb | Jbe | Jc | Je | Jg | Jge | Jl | Jle | Jna | 
    Jnae | Jnb | Jnbe | Jnc | Jne | Jng | Jnge | Jnl | Jnle | Jno | 
    Jnp | Jns | Jnz | Jo | Jp | Jpe | Jpo | Js | Jz | Jmp | 
    Lahf | Lds | Lea | Les | Lock | Lodsb | Lodsw | Loop | Loope | Loopne | 
    Loopnz | Loopz | Mov | Movsb | Movsw | Mul | Neg | Nop | Not | Or |
    Out | Pop | Popf | Push | Pushf | Rcl | Rcr | Ret | Retn | Retf | 
    Rol | Ror | Sahf | Sal | Sar | Sbb | Scasb | Scasw | Shl | Shr | 
    Stc | Std | Sti | Stosb | Stosw | Sub | Test | Wait | Xchg | Xlat | 
    Xor

datatype instr_mnemonic_8088_x87 =
F2xm1 | Fabs  | Fadd  | Faddp  | Fbld  | Fbstp  | Fchs  | Fclex  | Fcom  | Fcomp  | Fcompp  | 
Decstp  | Fdisi  | Fdiv  | Fdivp  | Fdivr  | Fdivrp  | Feni  | Ffree  | Fiadd  | Ficom  |
Ficomp  | Fidiv  | Fidivr  | Fild  | Fimul  | Fincstp  | Finit  | Fist  | Fistp  | Fisub  | 
Isubr  | Fld  | Fld1  | Fldcw  | Fldenv  | Fldenvw  | Fldl2e  | Fldl2t  | Fldlg2  | Fldln2  | 
Ldpi  | Fldz  | Fmul  | Fmulp  | Fnclex  | Fndisi  | Fneni  | Fninit  | Fnop  | Fnsave  | Fnsavew  |
Fnstcw  | Fnstenv  | Fnstenvw  | Fnstsw  | Fpatan  | Fprem  | Fptan  | Frndint  | Frstor  | Frstorw  | 
Save  | Fsavew  | Fscale  | Fsqrt  | Fst  | Fstcw  | Fstenv  | Fstenvw  | Fstp  | Fstsw  | Fsub  |
Fsubp  | Fsubr  | Fsubrp  | Ftst  | Fwait  | Fxam  | Fxch  | Fxtract  | Fyl2x  | Fyl2xp1  

datatype instr_mnemonic_80188 =
  Bound | Enter | Ins | Leave | Outs | Popa | Pusha 

  datatype instr_mnemonic_80286 =
  Arpl | Clts | Lar | Lgdt | Lidt | Lldt | Lmsw | Loadall | Lsl | Ltr | Sgdt | Sidt | Sldt | Smsw
  | Str | Verr | Verw

datatype instr_mnemonic_80286_x87 = Fsetpm

datatype instr_mnemonic_80386 =
  Bsf | Bsr | Bt | Btc | Btr | Bts | Cdq |  Cwde | Ibts | Insd | Iretd | Iretf | Jecxz | Lfs | 
  Lgs | Lss | Lodsd | Loopw | Loopzw | Loopew | Loopnzw | Loopnew | Loopd | Loopzd | Looped | 
  Loopnzd | Loopned |  Movsx | Movzx | Outsd | Popad | Popfd | Pushad | Pushfd | Scasd | 
  Seta |  Setae |  Setb |  Setbe |  Setc |  Sete |  Setg |  Setge |  Setl |  Setle |  Setna |  Setnae |  Setnb |  Setnbe |  
  Setnc |  Setne |  Setng |  Setnge |  Setnl |  Setnle |  Setno |  Setnp |  Setns |  Setnz |  Seto |  Setp |  Setpe |  Setpo |  
  Sets |  Setz

datatype instr_mnemonic_80386_x87 =
  Fcos | Fldenvd | Fsaved | Fstenvd | Fprem1 | Frstord | Fsin | Fsincos | Fucom | Fucomp | Fucompp

datatype instr_mnemonic_80486 =
  instr_mnemonic_80386 | 
  Bswap | Cmpxchg | Invd | Invlpg | Wbinvd | Xadd

datatype instr_mnemonic_pentium =
  Cpuid | Cmpxchg8b | Rdmsr | Rdtsc | Wrmsr | Rsm

datatype instr_mnemonic_pentiummmx =
  Rdpmc

datatype instr_mnemonic_pentiummmx_mmx =
  Emms | Movd | Movq | Packssdw | Packsswb | Packuswb | Paddb | Paddw | Paddd | Paddq | Paddsb | 
  Paddsw | Paddusb | Paddusw | Pand | Pandn | Por | Pxor | Pcmpeqb | Pcmpeqw | Pcmpeqd | Pcmpgtb | 
  Pcmpgtw | Pcmpgtd | Pmaddwd | Pmulhw | Pmullw | Psllw | Pslld | Psllq | Psrad | Psraw | Psrlw | 
  Psrld | Psrlq | Psubb | Psubw | Psubd | Psubsb | Psubsw | Psubusb | Psubusw | Punpckhbw | 
  Punpckhwd | Punpckhdq | Punpcklbw | Punpcklwd | Punpckldq

datatype instr_mnemonic_pentiumpro =
  Cmova |  Cmovae |  Cmovb |  Cmovbe |  Cmovc |  Cmove |  Cmovg |  Cmovge |  Cmovl |  Cmovle | 
  Cmovna |  Cmovnae |  Cmovnb |  Cmovnbe |  Cmovnc |  Cmovne |  Cmovng |  Cmovnge |  Cmovnl |  
  Cmovnle |  Cmovno |  Cmovnp |  Cmovns |  Cmovnz |  Cmovo |  Cmovp |  Cmovpe |  Cmovpo |  Cmovs |  
  Cmovz | Ud2

datatype instr_mnemonic_pentiumpro_x87 =
  Fcmovb | Fcmovbe | Fcmove | Fcmovnb | Fcmovnbe | Fcmovne | Fcmovnu | Fcmovu | Fcomi | Fcomip | 
  Fucomi | Fucomip

datatype instr_mnemonic_pentiumii =
  Sysenter | Sysexit

  
datatype instr_mnemonic_sse =
  Maskmovq | Movntq | Prefetcht0 | Prefetcht1 | Prefetcht2 | Prefetchnta | Sfence

datatype instr_mnemonic_sse_x87 =
  Fxrstor | Fxsave 

datatype instr_mnemonic_sse_simdmmx =
  Pshufw | Pinsrw | Pextrw | Pmovmskb | Pminub | Pmaxub | Pavgb | Pavgw | Pmulhuw | Pminsw | Pmaxsw |
  Psadbw 

datatype instr_mnemonic_sse_simd =
  Andps | Andnps | Orps | Xorps | Movups | Movss | Movhlps | Movlps | Unpcklps | Unpckhps | Movlhps | 
  Movhps  | Movaps | Movmskps | Cvtpi2ps | Cvtsi2ss | Movntps | Cvttps2pi  | Cvttss2si  | Cvtps2pi | Cvtss2si  | Ucomiss | 
  Comiss | Sqrtps | Sqrtss | Rsqrtps | Rsqrtss | Rcpps | Rcpss | Addps | Addss | Mulps | Mulss |
  Subps | Subss | Minps | Minss | Divps | Divss | Maxps | Maxss | Ldmxcsr | Stmxcsr | Cmpps | Cmpss | 
  Shufps

datatype instr_mnemonic_sse2 =
  Clflush | Lfence | Mfence | Movnti | Pause

datatype instr_mnemonic_sse2_simdmmx =
  Psubq | Pmuludq 

datatype instr_mnemonic_sse2_simd =
 Movapd | Movntpd | Movhpd | Movlpd | Movupd | Movmskpd | Movsd | Addpd | Addsd | Divpd | Divsd | 
 Maxpd | Maxsd | Minpd | Minsd | Mulpd | Mulsd | Sqrtpd | Sqrtsd | Subpd | Subsd | Andpd | Andnpd | 
 Orpd | Xorpd | Cmppd | Cmpsd | Comisd | Ucomisd | Shufpd | Unpckhpd | Unpcklpd | Cvtdq2pd | Cvtdq2ps | 
 Cvtpd2dq | Cvtpd2pi | Cvtpd2ps | Cvtpi2pd | Cvtps2dq | Cvtps2pd | Cvtsd2si | Cvtsd2ss | Cvtsi2sd | 
 Cvtss2sd | Cvttpd2dq | Cvttpd2pi | Cvttps2dq | Cvttsd2si | Maskmovdqu | Movdq2q | 
 Movdqa | Movdqu | Movq2dq | Movntdq | Pshufhw | Pshuflw | Pshufd | Pslldq | Psrldq | Punpckhqdq | Punpcklqdq 

datatype instr_mnemonic_x86_64 =
  Cdqe | Cqo | Cmpsq | Cmpxchg16b | Iretq | Jrcxz | Lodsq | Movsxd | Popfq | Pushfq | Rdtscp | Scasq | Stosq | Swapgs 

datatype instr_mnemonic_sse3 =
  Monitor | Mwait 

datatype instr_mnemonic_sse3_x87 =
  Fisttp

datatype instr_mnemonic_sse3_simd =
  Addsubps | Addsubpd | Movddup | Movsldup | Movshdup | Haddps | Haddpd | Hsubps | Hsubpd | Lddqu 

datatype instr_mnemonic_ssse3_simdmmx =
  Psignb | Psignw | Psignd | Pshufb | Pmulhrsw | Pmaddubsw | Phsubw | Phsubsw | Phsubd | Phaddsw | Phaddw | Phaddd | Palignr | Pabsb | Pabsw | Pabsd 

datatype instr_mnemonic_sse41_simd =
  Dpps | Dppd | Blendps | Blendvps | Blendpd | Blendvpd | Roundps | Roundss | Roundpd | Roundsd | 
  Insertps | Extractps | 
  Mpsadbw | Phminposuw | Pmulld | Pmuldq | Pblendvb | Pblendw | Pminsb | Pminuw | Pminsd | Pminud | 
  Pmaxsb | Pmaxuw | Pmaxsd | Pmaxud | Pinsrb | Pinsrd | Pinsrq | Pextrb | Pextrd | Pextrq | 
  Pmovsxbw | Pmovzxbw | Pmovsxbd | Pmovzxbd | Pmovsxbq | Pmovzxbq | Pmovsxwd | Pmovzxwd | Pmovsxwq | 
  Pmovzxwq | Pmovsxdq | Pmovzxdq | Ptest | Pcmpeqq | Packusdw | Movntdqa 

datatype instr_mnemonic_vtx =
  Vmptrld | Vmptrst | Vmclear | Vmread | Vmwrite | Vmcall | Vmlaunch | Vmresume | Vmxoff | Vmxon |
  Vmfunc | Invvpid | Invept

datatype instr_mnemonic_sse42 =
  Crc32 | Popcnt

datatype instr_mnemonic_sse42_simd =
  Pcmpestri | Pcmpestrm | Pcmpistri | Pcmpistrm | Pcmpgtq 

datatype instr_mnemonic_avx_group1 =
  Vsqrtps | Vsqrtpd | Vrsqrtps | Vrcpps | Vaddps | Vaddpd | Vsubps | Vsubpd | Vmulps | Vmulpd | 
  Vdivps | Vdivpd | Vcvtps2pd | Vcvtpd2ps | Vcvtdq2ps | Vcvtps2dq | Vcvttps2dq | Vcvttpd2dq | 
  Vcvtpd2dq | Vcvtdq2pd | Vminps | Vminpd | Vmaxps | Vmaxpd | Vhaddpd | Vhaddps | Vhsubpd | Vhsubps |
  Vcmpps | Vcmppd | Vaddsubpd | Vaddsubps | Vdpps | Vroundpd | Vroundps | 
  Vmovaps | Vmovapd | Vmovdqa | Vmovups | Vmovupd | Vmovdqu | Vmovmskps | Vmovmskpd | 
  Vlddqu | Vmovntps | Vmovntpd | Vmovntdq | Vmovntdqa | Vmovshdup | Vmovsldup | Vmovddup | 
  Vunpckhpd | Vunpckhps | Vunpcklpd | Vblendps | Vblendpd | Vshufpd | Vshufps | Vunpcklps | 
  Vblendvps | Vblendvpd | Vptest | Vxorps | Vxorpd | Vorps | Vorpd | Vandnpd | Vandnps | Vandpd | Vandps | 
  Vbroadcastf128 |  Vbroadcastsd | Vbroadcastss | Vextractf128 | Vinsertf128 | Vmaskmovps | Vmaskmovpd |
  Vpermilpd | Vpermilps | Vperm2f128 | Vtestps | Vtestpd | Vzeroall | Vzeroupper |
  Vcvtsi2ss | Vcvtsi2sd | Vcvtsd2si | Vcvttss2si | Vcvttsd2si | Vcvtss2si | Vcomisd | Vrsqrtss | 
  Vrcpss | Vucomiss | Vucomisd | Vcomiss | Vaddss | Vaddsd | Vsubss | Vsubsd | Vmulss | Vmulsd | 
  Vdivss | Vdivsd | Vsqrtss | Vsqrtsd | Vcvtss2sd | Vcvtsd2ss | Vminss | Vminsd | Vmaxss | Vmaxsd | 
  Vpand | Vpandn | Vpor | Vpxor | Vpcmpgtb | Vpcmpgtw | Vpcmpgtd | Vpmaddwd | Vpmaddubsw | Vpavgb | 
  Vpavgw | Vpmuludq | Vpcmpeqb | Vpcmpeqw | Vpcmpeqd | Vpmullw | Vpmulhuw | Vpmulhw | Vpsubsw 

datatype instr_mnemonic_avx_group2 =
  Vpaddsw | Vpsadbw | Vpaddusb | Vpaddusw | Vpaddsb | Vpsubusb | Vpsubusw | Vpsubsb | Vpminub |
  Vpminsw | Vpmaxub | Vpmaxsw | Vpaddb | Vpaddw | Vpaddd | Vpaddq | Vpsubb | Vpsubw | Vpsubd | Vpsubq | 
  Vpsllw | Vpslld | Vpsllq | Vpsraw | Vpsrlw | Vpsrld | Vpsrlq | Vpsrad | Vphsubw | Vphsubd | Vphsubsw | 
  Vphaddw | Vphaddd | Vphaddsw | Vpmulhrsw | Vpsignb | Vpsignw | Vpsignd | Vpabsb | Vpabsw | Vpabsd |
  Vdppd | Vphminposuw | Vmpsadbw | Vpmaxsb | Vpmaxsd | Vpmaxud | Vpminsb | Vpminsd | Vpminud | Vpmaxuw |
  Vpminuw | Vpmovsxbw | Vpmovzxbw | Vpmovsxbd | Vpmovzxbd | Vpmovsxbq | Vpmovzxbq | Vpmovsxwd | Vpmovzxwd | Vpmovsxwq | 
  Vpmovzxwq | Vpmovsxdq | Vpmovzxdq | Vpmuldq | Vpmulld | Vroundsd | Vroundss | Vpopcnt | Vpcmpgtq |
  Vpcmpestri | Vpcmpestrm | Vpcmpistri | Vpcmpistrm | Vpclmulqdq | Vaesdec | Vaesdeclast | Vaesenc |
  Vaesenclast | Vaesimx | Vaeskeygenassist |
  Vstmxcsr | Vmovss | Vmovsd | Vcmpss | Vcmpsd | Vmovhps | Vmovhpd | Vmovlps | Vmovlpd | 
  Vmovlhps | Vmovhlps | Vmovq | Vmovd | Vpackuswb | Vpackssdw | Vpacksswb | Vpunpckhbw | Vpunpckhwd | 
  Vpunpcklbw | Vpunpcklwd | Vpunpckhdq | Vpunpckldq | Vpunpcklqdq | Vpunpckhqdq | Vpshufhw | Vpshuflw | 
  Vpshufd | Vpmovmskb | Vmaskmovdqu | Vpinsrw | Vpextrw | Vpalignr | 
  Vpshufb | Vextractps | Vinsertps | Vpackusdw | Vpcmpeqq | Vpblendvb | Vpblendw | Vpextrb | 
  Vpextrd | Vpextrq | Vpinsrb | Vpinsrd | Vpinsrq 

datatype instr_mnemonic_fma =
  Vfmadd132pd | Vfmadd213pd | Vfmadd231pd | Vfmadd132ps | Vfmadd213ps | Vfmadd231ps | Vfmadd132sd | 
Vfmadd213sd | Vfmadd231sd | Vfmadd132ss | Vfmadd213ss | Vfmadd231ss | Vfmaddsub132pd | Vfmaddsub213pd | 
Vfmaddsub231pd | Vfmaddsub132ps | Vfmaddsub213ps | Vfmaddsub231ps | Vfmsubadd132pd | Vfmsubadd213pd | 
Vfmsubadd231pd | Vfmsubadd132ps | Vfmsubadd213ps | Vfmsubadd231ps | Vfmsub132pd | Vfmsub213pd | 
Vfmsub231pd | Vfmsub132ps | Vfmsub213ps | Vfmsub231ps | Vfmsub132sd | Vfmsub213sd | Vfmsub231sd | 
Vfmsub132ss | Vfmsub213ss | Vfmsub231ss | Vfnmadd132pd | Vfnmadd213pd | Vfnmadd231pd | Vfnmadd132ps | 
Vfnmadd213ps | Vfnmadd231ps | Vfnmadd132sd | Vfnmadd213sd | Vfnmadd231sd | Vfnmadd132ss | Vfnmadd213ss | 
Vfnmadd231ss | Vfnmsub132pd | Vfnmsub213pd | Vfnmsub231pd | Vfnmsub132ps | Vfnmsub213ps | Vfnmsub231ps | 
Vfnmsub132sd | Vfnmsub213sd | Vfnmsub231sd | Vfnmsub132ss | Vfnmsub213ss | Vfnmsub231ss 

datatype instr_mnemonic_bm1_bm2 =
  Andn | Bextr | Blsi | Blsmsk | Blsr | Bzhi | Lzcnt | Mulx | Pdep | Pext | Rorx | Sarx | Shlx | Shrx | Tzcnt

datatype instr_mnemonic_avx512_f_cd = NopAVX512_F_CD 
datatype instr_mnemonic_avx512_vl_dq_bw =
  Vpbroadcastb | Vpbroadcastd | Vpbroadcastq | Vpbroadcastw 

(* MNEMONICS BEGIN *)
datatype instr_mnemonic = 
        IS_8088             of instr_mnemonic_8088 | 
        IS_8088_x87         of instr_mnemonic_8088_x87 | 
        IS_80188            of instr_mnemonic_80188 |
        IS_80286            of instr_mnemonic_80286 | 
        IS_80286_x87        of instr_mnemonic_80286_x87 | 
        IS_80386            of instr_mnemonic_80386 |
        IS_80386_x87        of instr_mnemonic_80386_x87 | 
        IS_80486            of instr_mnemonic_80486 |
        IS_Pentium          of instr_mnemonic_pentium |  
        IS_PentiumMMX       of instr_mnemonic_pentiummmx |  
        IS_PentiumMMX_MMX   of instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       of instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   of instr_mnemonic_pentiumpro_x87 | 
        IS_PentiumII        of instr_mnemonic_pentiumii | 
        IS_SSE              of instr_mnemonic_sse | 
        IS_SSE_x87          of instr_mnemonic_sse_x87 | 
        IS_SSE_SIMDMMX      of instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         of instr_mnemonic_sse_simd |
        IS_SSE2              of instr_mnemonic_sse2 | 
        IS_SSE2_SIMDMMX     of instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        of instr_mnemonic_sse2_simd |
        IS_SSE3             of instr_mnemonic_sse3 | 
        IS_SSE3_x87         of instr_mnemonic_sse3_x87 | 
        IS_SSE3_SIMD        of instr_mnemonic_sse3_simd |
        IS_X86_64           of instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    of instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      of instr_mnemonic_sse41_simd | 
        IS_VT_X             of instr_mnemonic_vtx |  
        IS_SSE4_2            of instr_mnemonic_sse42 |
        IS_SSE4_2_SIMD      of instr_mnemonic_sse42_simd | 
        IS_AVX              of instr_mnemonic_avx_group1 |
        IS_AVX_2            of instr_mnemonic_avx_group2 |
        IS_FMA              of instr_mnemonic_fma |
        IS_BM1_BM2          of instr_mnemonic_bm1_bm2 | 
        IS_AVX_512_F_CD     of instr_mnemonic_avx512_f_cd | 
        IS_AVX_512_VL_DQ_BW of instr_mnemonic_avx512_vl_dq_bw  

datatype instr_mnemonic_family = 
        IMF_8088 | IMF_8088_x87 | IMF_80188 | IMF_80286 | IMF_80286_x87 | IMF_80386 | IMF_80386_x87 
      | IMF_80486 | IMF_Pentium | IMF_PentiumMMX | IMF_PentiumMMX_MMX | IMF_PentiumPro | IMF_PentiumPro_x87 
      | IMF_PentiumII | IMF_SSE | IMF_SSE_x87 | IMF_SSE_SIMDMMX | IMF_SSE_SIMD | IMF_SSE2 | IMF_SSE2_SIMDMMX 
      | IMF_SSE2_SIMD | IMF_SSE3 | IMF_SSE3_x87 | IMF_SSE3_SIMD | IMF_X86_64 | IMF_SSSE3_SIMDMMX | IMF_SSE4_1_SIMD 
      | IMF_VT_X | IMF_SSE4_2 | IMF_SSE4_2_SIMD | IMF_AVX | IMF_AVX_2 | IMF_AVX2 | IMF_FMA | IMF_BM1_BM2 
      | IMF_AVX_512_F_CD | IMF_AVX_512_VL_DQ_BW   

datatype flag =
  flag_cf | flag_sf | flag_of | flag_af | flag_zf | flag_pf

fun
mk_instr_mnemonic_family (IMF_8088) = @{term "IMF_8088"}
 | mk_instr_mnemonic_family (IMF_8088_x87) = @{term "IMF_8088_x87"}
 | mk_instr_mnemonic_family (IMF_80188) = @{term "IMF_80188"}
 | mk_instr_mnemonic_family (IMF_80286) = @{term "IMF_80286"}
 | mk_instr_mnemonic_family (IMF_80286_x87) = @{term "IMF_80286_x87"}
 | mk_instr_mnemonic_family (IMF_80386) = @{term "IMF_80386"}
 | mk_instr_mnemonic_family (IMF_80386_x87) = @{term "IMF_80386_x87"}
 | mk_instr_mnemonic_family (IMF_80486) = @{term "IMF_80486"}
 | mk_instr_mnemonic_family (IMF_Pentium) = @{term "IMF_Pentium"}
 | mk_instr_mnemonic_family (IMF_PentiumMMX) = @{term "IMF_PentiumMMX"}
 | mk_instr_mnemonic_family (IMF_PentiumMMX_MMX) = @{term "IMF_PentiumMMX_MMX"}
 | mk_instr_mnemonic_family (IMF_PentiumPro) = @{term "IMF_PentiumPro"}
 | mk_instr_mnemonic_family (IMF_PentiumPro_x87) = @{term "IMF_PentiumPro_x87"}
 | mk_instr_mnemonic_family (IMF_PentiumII) = @{term "IMF_PentiumII"}
 | mk_instr_mnemonic_family (IMF_SSE) = @{term "IMF_SSE"}
 | mk_instr_mnemonic_family (IMF_SSE_x87) = @{term "IMF_SSE_x87"}
 | mk_instr_mnemonic_family (IMF_SSE_SIMDMMX) = @{term "IMF_SSE_SIMDMMX"}
 | mk_instr_mnemonic_family (IMF_SSE_SIMD) = @{term "IMF_SSE_SIMD"}
 | mk_instr_mnemonic_family (IMF_SSE2) = @{term "IMF_SSE2"}
 | mk_instr_mnemonic_family (IMF_SSE2_SIMDMMX) = @{term "IMF_SSE2_SIMDMMX"}
 | mk_instr_mnemonic_family (IMF_SSE2_SIMD) = @{term "IMF_SSE2_SIMD"}
 | mk_instr_mnemonic_family (IMF_SSE3) = @{term "IMF_SSE3"}
 | mk_instr_mnemonic_family (IMF_SSE3_x87) = @{term "IMF_SSE3_x87"}
 | mk_instr_mnemonic_family (IMF_SSE3_SIMD) = @{term "IMF_SSE3_SIMD"}
 | mk_instr_mnemonic_family (IMF_X86_64) = @{term "IMF_X86_64"}
 | mk_instr_mnemonic_family (IMF_SSSE3_SIMDMMX) = @{term "IMF_SSSE3_SIMDMMX"}
 | mk_instr_mnemonic_family (IMF_SSE4_1_SIMD) = @{term "IMF_SSE4_1_SIMD"}
 | mk_instr_mnemonic_family (IMF_VT_X) = @{term "IMF_VT_X"}
 | mk_instr_mnemonic_family (IMF_SSE4_2) = @{term "IMF_SSE4_2"}
 | mk_instr_mnemonic_family (IMF_SSE4_2_SIMD) = @{term "IMF_SSE4_2_SIMD"}
 | mk_instr_mnemonic_family (IMF_AVX) = @{term "IMF_AVX"}
 | mk_instr_mnemonic_family (IMF_AVX_2) = @{term "IMF_AVX_2"}
 | mk_instr_mnemonic_family (IMF_AVX2) = @{term "IMF_AVX2"}
 | mk_instr_mnemonic_family (IMF_FMA) = @{term "IMF_FMA"}
 | mk_instr_mnemonic_family (IMF_BM1_BM2) = @{term "IMF_BM1_BM2"}
 | mk_instr_mnemonic_family (IMF_AVX_512_F_CD) = @{term "IMF_AVX_512_F_CD"}
 | mk_instr_mnemonic_family (IMF_AVX_512_VL_DQ_BW) = @{term "IMF_AVX_512_VL_DQ_BW"}   

fun 
  mk_instr_mnemonic (IS_8088 Aaa) = @{term "IS_8088 Aaa"} |  mk_instr_mnemonic (IS_8088 Aad) = @{term "IS_8088 Aad"} |  mk_instr_mnemonic (IS_8088 Aam) = @{term "IS_8088 Aam"} |  mk_instr_mnemonic (IS_8088 Aas) = @{term "IS_8088 Aas"} |  mk_instr_mnemonic (IS_8088 Adc) = @{term "IS_8088 Adc"} |  mk_instr_mnemonic (IS_8088 Add) = @{term "IS_8088 Add"} |  mk_instr_mnemonic (IS_8088 And) = @{term "IS_8088 And"} 
|  mk_instr_mnemonic (IS_8088 Call) = @{term "IS_8088 Call"} |  mk_instr_mnemonic (IS_8088 Cbw) = @{term "IS_8088 Cbw"} |  mk_instr_mnemonic (IS_8088 Clc) = @{term "IS_8088 Clc"} |  mk_instr_mnemonic (IS_8088 Cld) = @{term "IS_8088 Cld"} |  mk_instr_mnemonic (IS_8088 Cli) = @{term "IS_8088 Cli"} |  mk_instr_mnemonic (IS_8088 Cmc) = @{term "IS_8088 Cmc"} |  mk_instr_mnemonic (IS_8088 Cmp) = @{term "IS_8088 Cmp"} 
|  mk_instr_mnemonic (IS_8088 Cmpsb) = @{term "IS_8088 Cmpsb"} |  mk_instr_mnemonic (IS_8088 Cwd) = @{term "IS_8088 Cwd"} |  mk_instr_mnemonic (IS_8088 Daa) = @{term "IS_8088 Daa"} |  mk_instr_mnemonic (IS_8088 Das) = @{term "IS_8088 Das"} |  mk_instr_mnemonic (IS_8088 Dec) = @{term "IS_8088 Dec"} |  mk_instr_mnemonic (IS_8088 Div) = @{term "IS_8088 Div"} |  mk_instr_mnemonic (IS_8088 Esc) = @{term "IS_8088 Esc"} 
|  mk_instr_mnemonic (IS_8088 Hlt) = @{term "IS_8088 Hlt"} |  mk_instr_mnemonic (IS_8088 Idiv) = @{term "IS_8088 Idiv"} |   mk_instr_mnemonic (IS_8088 Imul) = @{term "IS_8088 Imul"} |  mk_instr_mnemonic (IS_8088 In) = @{term "IS_8088 In"} |  mk_instr_mnemonic (IS_8088 Inc) = @{term "IS_8088 Inc"} |  mk_instr_mnemonic (IS_8088 INS_Int) = @{term "IS_8088 INS_Int"}  |  mk_instr_mnemonic (IS_8088 Into) = @{term "IS_8088 Into"} 
|  mk_instr_mnemonic (IS_8088 Iret) = @{term "IS_8088 Iret"} |  mk_instr_mnemonic (IS_8088 Ja) = @{term "IS_8088 Ja"} |  mk_instr_mnemonic (IS_8088 Jae) = @{term "IS_8088 Jae"} |  mk_instr_mnemonic (IS_8088 Jb) = @{term "IS_8088 Jb"} |  mk_instr_mnemonic (IS_8088 Jbe) = @{term "IS_8088 Jbe"} |  mk_instr_mnemonic (IS_8088 Jc) = @{term "IS_8088 Jc"} |  mk_instr_mnemonic (IS_8088 Je) = @{term "IS_8088 Je"} |  mk_instr_mnemonic (IS_8088 Jg) = @{term "IS_8088 Jg"} 
|  mk_instr_mnemonic (IS_8088 Jge) = @{term "IS_8088 Jge"} |  mk_instr_mnemonic (IS_8088 Jl) = @{term "IS_8088 Jl"} |  mk_instr_mnemonic (IS_8088 Jle) = @{term "IS_8088 Jle"} |  mk_instr_mnemonic (IS_8088 Jna) = @{term "IS_8088 Jna"} |  mk_instr_mnemonic (IS_8088 Jnae) = @{term "IS_8088 Jnae"} |  mk_instr_mnemonic (IS_8088 Jnb) = @{term "IS_8088 Jnb"} |  mk_instr_mnemonic (IS_8088 Jnbe) = @{term "IS_8088 Jnbe"} 
|  mk_instr_mnemonic (IS_8088 Jnc) = @{term "IS_8088 Jnc"} |  mk_instr_mnemonic (IS_8088 Jne) = @{term "IS_8088 Jne"} |  mk_instr_mnemonic (IS_8088 Jng) = @{term "IS_8088 Jng"} |  mk_instr_mnemonic (IS_8088 Jnge) = @{term "IS_8088 Jnge"} |   mk_instr_mnemonic (IS_8088 Jnl) = @{term "IS_8088 Jnl"} |  mk_instr_mnemonic (IS_8088 Jnle) = @{term "IS_8088 Jnle"} |  mk_instr_mnemonic (IS_8088 Jno) = @{term "IS_8088 Jno"} 
|  mk_instr_mnemonic (IS_8088 Jnp) = @{term "IS_8088 Jnp"} |  mk_instr_mnemonic (IS_8088 Jns) = @{term "IS_8088 Jns"} |  mk_instr_mnemonic (IS_8088 Jnz) = @{term "IS_8088 Jnz"} |  mk_instr_mnemonic (IS_8088 Jo) = @{term "IS_8088 Jo"} |  mk_instr_mnemonic (IS_8088 Jp) = @{term "IS_8088 Jp"} |  mk_instr_mnemonic (IS_8088 Jpe) = @{term "IS_8088 Jpe"} |  mk_instr_mnemonic (IS_8088 Jpo) = @{term "IS_8088 Jpo"} |  mk_instr_mnemonic (IS_8088 Js) = @{term "IS_8088 Js"} 
|  mk_instr_mnemonic (IS_8088 Jz) = @{term "IS_8088 Jz"} |  mk_instr_mnemonic (IS_8088 Jmp) = @{term "IS_8088 Jmp"} |  mk_instr_mnemonic (IS_8088 Lahf) = @{term "IS_8088 Lahf"} |  mk_instr_mnemonic (IS_8088 Lds) = @{term "IS_8088 Lds"} |  mk_instr_mnemonic (IS_8088 Lea) = @{term "IS_8088 Lea"} |  mk_instr_mnemonic (IS_8088 Les) = @{term "IS_8088 Les"} |  mk_instr_mnemonic (IS_8088 Lock) = @{term "IS_8088 Lock"} 
|  mk_instr_mnemonic (IS_8088 Lodsb) = @{term "IS_8088 Lodsb"} |  mk_instr_mnemonic (IS_8088 Lodsw) = @{term "IS_8088 Lodsw"} |  mk_instr_mnemonic (IS_8088 Loop) = @{term "IS_8088 Loop"} |  mk_instr_mnemonic (IS_8088 Loope) = @{term "IS_8088 Loope"} |   mk_instr_mnemonic (IS_8088 Loopne) = @{term "IS_8088 Loopne"} |  mk_instr_mnemonic (IS_8088 Loopnz) = @{term "IS_8088 Loopnz"} 
|  mk_instr_mnemonic (IS_8088 Loopz) = @{term "IS_8088 Loopz"} |  mk_instr_mnemonic (IS_8088 Mov) = @{term "IS_8088 Mov"} |  mk_instr_mnemonic (IS_8088 Movsb) = @{term "IS_8088 Movsb"} |  mk_instr_mnemonic (IS_8088 Movsw) = @{term "IS_8088 Movsw"} |  mk_instr_mnemonic (IS_8088 Mul) = @{term "IS_8088 Mul"} |  mk_instr_mnemonic (IS_8088 Neg) = @{term "IS_8088 Neg"} |  mk_instr_mnemonic (IS_8088 Nop) = @{term "IS_8088 Nop"} 
|  mk_instr_mnemonic (IS_8088 Not) = @{term "IS_8088 Not"} |  mk_instr_mnemonic (IS_8088 Or) = @{term "IS_8088 Or"} |  mk_instr_mnemonic (IS_8088 Out) = @{term "IS_8088 Out"} |  mk_instr_mnemonic (IS_8088 Pop) = @{term "IS_8088 Pop"} |  mk_instr_mnemonic (IS_8088 Popf) = @{term "IS_8088 Popf"} |  mk_instr_mnemonic (IS_8088 Push) = @{term "IS_8088 Push"} |  mk_instr_mnemonic (IS_8088 Pushf) = @{term "IS_8088 Pushf"} 
|  mk_instr_mnemonic (IS_8088 Rcl) = @{term "IS_8088 Rcl"} |  mk_instr_mnemonic (IS_8088 Rcr) = @{term "IS_8088 Rcr"} |  mk_instr_mnemonic (IS_8088 Ret) = @{term "IS_8088 Ret"} |  mk_instr_mnemonic (IS_8088 Retn) = @{term "IS_8088 Retn"} |  mk_instr_mnemonic (IS_8088 Retf) = @{term "IS_8088 Retf"} |   mk_instr_mnemonic (IS_8088 Rol) = @{term "IS_8088 Rol"} |  mk_instr_mnemonic (IS_8088 Ror) = @{term "IS_8088 Ror"} 
|  mk_instr_mnemonic (IS_8088 Sahf) = @{term "IS_8088 Sahf"} |  mk_instr_mnemonic (IS_8088 Sal) = @{term "IS_8088 Sal"} |  mk_instr_mnemonic (IS_8088 Sar) = @{term "IS_8088 Sar"} |  mk_instr_mnemonic (IS_8088 Sbb) = @{term "IS_8088 Sbb"} |  mk_instr_mnemonic (IS_8088 Scasb) = @{term "IS_8088 Scasb"} |  mk_instr_mnemonic (IS_8088 Scasw) = @{term "IS_8088 Scasw"} |  mk_instr_mnemonic (IS_8088 Shl) = @{term "IS_8088 Shl"} 
|  mk_instr_mnemonic (IS_8088 Shr) = @{term "IS_8088 Shr"} |  mk_instr_mnemonic (IS_8088 Stc) = @{term "IS_8088 Stc"} |  mk_instr_mnemonic (IS_8088 Std) = @{term "IS_8088 Std"} |  mk_instr_mnemonic (IS_8088 Sti) = @{term "IS_8088 Sti"} |  mk_instr_mnemonic (IS_8088 Stosb) = @{term "IS_8088 Stosb"} |  mk_instr_mnemonic (IS_8088 Stosw) = @{term "IS_8088 Stosw"} |  mk_instr_mnemonic (IS_8088 Sub) = @{term "IS_8088 Sub"} 
|  mk_instr_mnemonic (IS_8088 Test) = @{term "IS_8088 Test"} |  mk_instr_mnemonic (IS_8088 Wait) = @{term "IS_8088 Wait"} |  mk_instr_mnemonic (IS_8088 Xchg) = @{term "IS_8088 Xchg"} |  mk_instr_mnemonic (IS_8088 Xlat) = @{term "IS_8088 Xlat"} |  mk_instr_mnemonic (IS_8088 Xor) = @{term "IS_8088 Xor"} |

  mk_instr_mnemonic (IS_8088_x87 F2xm1) = @{term "IS_8088_x87 F2xm1"} |  mk_instr_mnemonic (IS_8088_x87 Fabs) = @{term "IS_8088_x87 Fabs"} |  mk_instr_mnemonic (IS_8088_x87 Fadd) = @{term "IS_8088_x87 Fadd"} |  mk_instr_mnemonic (IS_8088_x87 Faddp) = @{term "IS_8088_x87 Faddp"} |  mk_instr_mnemonic (IS_8088_x87 Fbld) = @{term "IS_8088_x87 Fbld"} 
|  mk_instr_mnemonic (IS_8088_x87 Fbstp) = @{term "IS_8088_x87 Fbstp"} |  mk_instr_mnemonic (IS_8088_x87 Fchs) = @{term "IS_8088_x87 Fchs"} |  mk_instr_mnemonic (IS_8088_x87 Fclex) = @{term "IS_8088_x87 Fclex"} |  mk_instr_mnemonic (IS_8088_x87 Fcom) = @{term "IS_8088_x87 Fcom"} |  mk_instr_mnemonic (IS_8088_x87 Fcomp) = @{term "IS_8088_x87 Fcomp"} 
|  mk_instr_mnemonic (IS_8088_x87 Fcompp) = @{term "IS_8088_x87 Fcompp"} |  mk_instr_mnemonic (IS_8088_x87 Decstp) = @{term "IS_8088_x87 Decstp"} |  mk_instr_mnemonic (IS_8088_x87 Fdisi) = @{term "IS_8088_x87 Fdisi"} |  mk_instr_mnemonic (IS_8088_x87 Fdiv) = @{term "IS_8088_x87 Fdiv"} |  mk_instr_mnemonic (IS_8088_x87 Fdivp) = @{term "IS_8088_x87 Fdivp"} 
|  mk_instr_mnemonic (IS_8088_x87 Fdivr) = @{term "IS_8088_x87 Fdivr"} |  mk_instr_mnemonic (IS_8088_x87 Fdivrp) = @{term "IS_8088_x87 Fdivrp"} |  mk_instr_mnemonic (IS_8088_x87 Feni) = @{term "IS_8088_x87 Feni"} |   mk_instr_mnemonic (IS_8088_x87 Ffree) = @{term "IS_8088_x87 Ffree"} |  mk_instr_mnemonic (IS_8088_x87 Fiadd) = @{term "IS_8088_x87 Fiadd"} 
|  mk_instr_mnemonic (IS_8088_x87 Ficom) = @{term "IS_8088_x87 Ficom"} |  mk_instr_mnemonic (IS_8088_x87 Ficomp) = @{term "IS_8088_x87 Ficomp"} |  mk_instr_mnemonic (IS_8088_x87 Fidiv) = @{term "IS_8088_x87 Fidiv"} |  mk_instr_mnemonic (IS_8088_x87 Fidivr) = @{term "IS_8088_x87 Fidivr"} |  mk_instr_mnemonic (IS_8088_x87 Fild) = @{term "IS_8088_x87 Fild"} 
|  mk_instr_mnemonic (IS_8088_x87 Fimul) = @{term "IS_8088_x87 Fimul"} |  mk_instr_mnemonic (IS_8088_x87 Fincstp) = @{term "IS_8088_x87 Fincstp"} |  mk_instr_mnemonic (IS_8088_x87 Finit) = @{term "IS_8088_x87 Finit"} |  mk_instr_mnemonic (IS_8088_x87 Fist) = @{term "IS_8088_x87 Fist"} |  mk_instr_mnemonic (IS_8088_x87 Fistp) = @{term "IS_8088_x87 Fistp"} 
|  mk_instr_mnemonic (IS_8088_x87 Fisub) = @{term "IS_8088_x87 Fisub"} |  mk_instr_mnemonic (IS_8088_x87 Isubr) = @{term "IS_8088_x87 Isubr"} |  mk_instr_mnemonic (IS_8088_x87 Fld) = @{term "IS_8088_x87 Fld"} |  mk_instr_mnemonic (IS_8088_x87 Fld1) = @{term "IS_8088_x87 Fld1"} |  mk_instr_mnemonic (IS_8088_x87 Fldcw) = @{term "IS_8088_x87 Fldcw"} 
|  mk_instr_mnemonic (IS_8088_x87 Fldenv) = @{term "IS_8088_x87 Fldenv"} |   mk_instr_mnemonic (IS_8088_x87 Fldenvw) = @{term "IS_8088_x87 Fldenvw"} |  mk_instr_mnemonic (IS_8088_x87 Fldl2e) = @{term "IS_8088_x87 Fldl2e"} |  mk_instr_mnemonic (IS_8088_x87 Fldl2t) = @{term "IS_8088_x87 Fldl2t"} |  mk_instr_mnemonic (IS_8088_x87 Fldlg2) = @{term "IS_8088_x87 Fldlg2"} 
|  mk_instr_mnemonic (IS_8088_x87 Fldln2) = @{term "IS_8088_x87 Fldln2"} |  mk_instr_mnemonic (IS_8088_x87 Ldpi) = @{term "IS_8088_x87 Ldpi"} |  mk_instr_mnemonic (IS_8088_x87 Fldz) = @{term "IS_8088_x87 Fldz"} |  mk_instr_mnemonic (IS_8088_x87 Fmul) = @{term "IS_8088_x87 Fmul"} |  mk_instr_mnemonic (IS_8088_x87 Fmulp) = @{term "IS_8088_x87 Fmulp"} 
|  mk_instr_mnemonic (IS_8088_x87 Fnclex) = @{term "IS_8088_x87 Fnclex"} |  mk_instr_mnemonic (IS_8088_x87 Fndisi) = @{term "IS_8088_x87 Fndisi"} |  mk_instr_mnemonic (IS_8088_x87 Fneni) = @{term "IS_8088_x87 Fneni"} |  mk_instr_mnemonic (IS_8088_x87 Fninit) = @{term "IS_8088_x87 Fninit"} |  mk_instr_mnemonic (IS_8088_x87 Fnop) = @{term "IS_8088_x87 Fnop"} 
|  mk_instr_mnemonic (IS_8088_x87 Fnsave) = @{term "IS_8088_x87 Fnsave"} |  mk_instr_mnemonic (IS_8088_x87 Fnsavew) = @{term "IS_8088_x87 Fnsavew"} |  mk_instr_mnemonic (IS_8088_x87 Fnstcw) = @{term "IS_8088_x87 Fnstcw"} |   mk_instr_mnemonic (IS_8088_x87 Fnstenv) = @{term "IS_8088_x87 Fnstenv"} 
|  mk_instr_mnemonic (IS_8088_x87 Fnstenvw) = @{term "IS_8088_x87 Fnstenvw"} |  mk_instr_mnemonic (IS_8088_x87 Fnstsw) = @{term "IS_8088_x87 Fnstsw"} |  mk_instr_mnemonic (IS_8088_x87 Fpatan) = @{term "IS_8088_x87 Fpatan"} |  mk_instr_mnemonic (IS_8088_x87 Fprem) = @{term "IS_8088_x87 Fprem"} |  mk_instr_mnemonic (IS_8088_x87 Fptan) = @{term "IS_8088_x87 Fptan"} 
|  mk_instr_mnemonic (IS_8088_x87 Frndint) = @{term "IS_8088_x87 Frndint"} |  mk_instr_mnemonic (IS_8088_x87 Frstor) = @{term "IS_8088_x87 Frstor"} |  mk_instr_mnemonic (IS_8088_x87 Frstorw) = @{term "IS_8088_x87 Frstorw"} |  mk_instr_mnemonic (IS_8088_x87 Save) = @{term "IS_8088_x87 Save"} |  mk_instr_mnemonic (IS_8088_x87 Fsavew) = @{term "IS_8088_x87 Fsavew"} 
|  mk_instr_mnemonic (IS_8088_x87 Fscale) = @{term "IS_8088_x87 Fscale"} |  mk_instr_mnemonic (IS_8088_x87 Fsqrt) = @{term "IS_8088_x87 Fsqrt"} |  mk_instr_mnemonic (IS_8088_x87 Fst) = @{term "IS_8088_x87 Fst"} |  mk_instr_mnemonic (IS_8088_x87 Fstcw) = @{term "IS_8088_x87 Fstcw"} |  mk_instr_mnemonic (IS_8088_x87 Fstenv) = @{term "IS_8088_x87 Fstenv"} 
|  mk_instr_mnemonic (IS_8088_x87 Fstenvw) = @{term "IS_8088_x87 Fstenvw"} |  mk_instr_mnemonic (IS_8088_x87 Fstp) = @{term "IS_8088_x87 Fstp"} |  mk_instr_mnemonic (IS_8088_x87 Fstsw) = @{term "IS_8088_x87 Fstsw"} |  mk_instr_mnemonic (IS_8088_x87 Fsub) = @{term "IS_8088_x87 Fsub"} |  mk_instr_mnemonic (IS_8088_x87 Fsubp) = @{term "IS_8088_x87 Fsubp"} 
|  mk_instr_mnemonic (IS_8088_x87 Fsubr) = @{term "IS_8088_x87 Fsubr"} |  mk_instr_mnemonic (IS_8088_x87 Fsubrp) = @{term "IS_8088_x87 Fsubrp"} |  mk_instr_mnemonic (IS_8088_x87 Ftst) = @{term "IS_8088_x87 Ftst"} |  mk_instr_mnemonic (IS_8088_x87 Fwait) = @{term "IS_8088_x87 Fwait"} |  mk_instr_mnemonic (IS_8088_x87 Fxam) = @{term "IS_8088_x87 Fxam"} 
|  mk_instr_mnemonic (IS_8088_x87 Fxch) = @{term "IS_8088_x87 Fxch"} |  mk_instr_mnemonic (IS_8088_x87 Fxtract) = @{term "IS_8088_x87 Fxtract"} |  mk_instr_mnemonic (IS_8088_x87 Fyl2x) = @{term "IS_8088_x87 Fyl2x"} |  mk_instr_mnemonic (IS_8088_x87 Fyl2xp1) = @{term "IS_8088_x87 Fyl2xp1"} | 

  mk_instr_mnemonic (IS_80188 Bound) = @{term "IS_80188 Bound"} |  mk_instr_mnemonic (IS_80188 Enter) = @{term "IS_80188 Enter"} |  mk_instr_mnemonic (IS_80188 Ins) = @{term "IS_80188 Ins"} |  mk_instr_mnemonic (IS_80188 Leave) = @{term "IS_80188 Leave"} |  mk_instr_mnemonic (IS_80188 Outs) = @{term "IS_80188 Outs"} |  mk_instr_mnemonic (IS_80188 Popa) = @{term "IS_80188 Popa"} 
|  mk_instr_mnemonic (IS_80188 Pusha) = @{term "IS_80188 Pusha"} | 

  mk_instr_mnemonic (IS_80286 Arpl) = @{term "IS_80286 Arpl"} |  mk_instr_mnemonic (IS_80286 Clts) = @{term "IS_80286 Clts"} |  mk_instr_mnemonic (IS_80286 Lar) = @{term "IS_80286 Lar"} |  mk_instr_mnemonic (IS_80286 Lgdt) = @{term "IS_80286 Lgdt"} |  mk_instr_mnemonic (IS_80286 Lidt) = @{term "IS_80286 Lidt"} |  mk_instr_mnemonic (IS_80286 Lldt) = @{term "IS_80286 Lldt"} 
|  mk_instr_mnemonic (IS_80286 Lmsw) = @{term "IS_80286 Lmsw"} |  mk_instr_mnemonic (IS_80286 Loadall) = @{term "IS_80286 Loadall"} |  mk_instr_mnemonic (IS_80286 Lsl) = @{term "IS_80286 Lsl"} |  mk_instr_mnemonic (IS_80286 Ltr) = @{term "IS_80286 Ltr"} |  mk_instr_mnemonic (IS_80286 Sgdt) = @{term "IS_80286 Sgdt"} |  mk_instr_mnemonic (IS_80286 Sidt) = @{term "IS_80286 Sidt"} 
|  mk_instr_mnemonic (IS_80286 Sldt) = @{term "IS_80286 Sldt"} |  mk_instr_mnemonic (IS_80286 Smsw) = @{term "IS_80286 Smsw"} |  mk_instr_mnemonic (IS_80286 Str) = @{term "IS_80286 Str"} |  mk_instr_mnemonic (IS_80286 Verr) = @{term "IS_80286 Verr"} |  mk_instr_mnemonic (IS_80286 Verw) = @{term "IS_80286 Verw"} |

  mk_instr_mnemonic (IS_80286_x87 Fsetpm) = @{term "IS_80286_x87 Fsetpm"} |

  mk_instr_mnemonic (IS_80386 Bsf) = @{term "IS_80386 Bsf"} |  mk_instr_mnemonic (IS_80386 Bsr) = @{term "IS_80386 Bsr"} |  mk_instr_mnemonic (IS_80386 Bt) = @{term "IS_80386 Bt"} |  mk_instr_mnemonic (IS_80386 Btc) = @{term "IS_80386 Btc"} |  mk_instr_mnemonic (IS_80386 Btr) = @{term "IS_80386 Btr"} |  mk_instr_mnemonic (IS_80386 Bts) = @{term "IS_80386 Bts"} |  mk_instr_mnemonic (IS_80386 Cdq) = @{term "IS_80386 Cdq"} 
|  mk_instr_mnemonic (IS_80386 Cwde) = @{term "IS_80386 Cwde"} |  mk_instr_mnemonic (IS_80386 Ibts) = @{term "IS_80386 Ibts"} |  mk_instr_mnemonic (IS_80386 Insd) = @{term "IS_80386 Insd"} |  mk_instr_mnemonic (IS_80386 Iretd) = @{term "IS_80386 Iretd"} |  mk_instr_mnemonic (IS_80386 Iretf) = @{term "IS_80386 Iretf"} |  mk_instr_mnemonic (IS_80386 Jecxz) = @{term "IS_80386 Jecxz"} 
|  mk_instr_mnemonic (IS_80386 Lfs) = @{term "IS_80386 Lfs"} |  mk_instr_mnemonic (IS_80386 Lgs) = @{term "IS_80386 Lgs"} |  mk_instr_mnemonic (IS_80386 Lss) = @{term "IS_80386 Lss"} |  mk_instr_mnemonic (IS_80386 Lodsd) = @{term "IS_80386 Lodsd"} |  mk_instr_mnemonic (IS_80386 Loopw) = @{term "IS_80386 Loopw"} |  mk_instr_mnemonic (IS_80386 Loopzw) = @{term "IS_80386 Loopzw"} 
|  mk_instr_mnemonic (IS_80386 Loopew) = @{term "IS_80386 Loopew"} |   mk_instr_mnemonic (IS_80386 Loopnzw) = @{term "IS_80386 Loopnzw"} |  mk_instr_mnemonic (IS_80386 Loopnew) = @{term "IS_80386 Loopnew"} |  mk_instr_mnemonic (IS_80386 Loopd) = @{term "IS_80386 Loopd"} |  mk_instr_mnemonic (IS_80386 Loopzd) = @{term "IS_80386 Loopzd"} 
|  mk_instr_mnemonic (IS_80386 Looped) = @{term "IS_80386 Looped"} |  mk_instr_mnemonic (IS_80386 Loopnzd) = @{term "IS_80386 Loopnzd"} |  mk_instr_mnemonic (IS_80386 Loopned) = @{term "IS_80386 Loopned"} |  mk_instr_mnemonic (IS_80386 Movsx) = @{term "IS_80386 Movsx"} |  mk_instr_mnemonic (IS_80386 Movzx) = @{term "IS_80386 Movzx"} 
|  mk_instr_mnemonic (IS_80386 Outsd) = @{term "IS_80386 Outsd"} |  mk_instr_mnemonic (IS_80386 Popad) = @{term "IS_80386 Popad"} |  mk_instr_mnemonic (IS_80386 Popfd) = @{term "IS_80386 Popfd"} |  mk_instr_mnemonic (IS_80386 Pushad) = @{term "IS_80386 Pushad"} |  mk_instr_mnemonic (IS_80386 Pushfd) = @{term "IS_80386 Pushfd"} 
|  mk_instr_mnemonic (IS_80386 Scasd) = @{term "IS_80386 Scasd"} |  mk_instr_mnemonic (IS_80386 Seta) = @{term "IS_80386 Seta"} |   mk_instr_mnemonic (IS_80386 Setae) = @{term "IS_80386 Setae"} |  mk_instr_mnemonic (IS_80386 Setb) = @{term "IS_80386 Setb"} |  mk_instr_mnemonic (IS_80386 Setbe) = @{term "IS_80386 Setbe"} |  mk_instr_mnemonic (IS_80386 Setc) = @{term "IS_80386 Setc"} 
|  mk_instr_mnemonic (IS_80386 Sete) = @{term "IS_80386 Sete"} |  mk_instr_mnemonic (IS_80386 Setg) = @{term "IS_80386 Setg"} |  mk_instr_mnemonic (IS_80386 Setge) = @{term "IS_80386 Setge"} |  mk_instr_mnemonic (IS_80386 Setl) = @{term "IS_80386 Setl"} |  mk_instr_mnemonic (IS_80386 Setle) = @{term "IS_80386 Setle"} |  mk_instr_mnemonic (IS_80386 Setna) = @{term "IS_80386 Setna"} 
|  mk_instr_mnemonic (IS_80386 Setnae) = @{term "IS_80386 Setnae"} |  mk_instr_mnemonic (IS_80386 Setnb) = @{term "IS_80386 Setnb"} |  mk_instr_mnemonic (IS_80386 Setnbe) = @{term "IS_80386 Setnbe"} |  mk_instr_mnemonic (IS_80386 Setnc) = @{term "IS_80386 Setnc"} |  mk_instr_mnemonic (IS_80386 Setne) = @{term "IS_80386 Setne"} |  mk_instr_mnemonic (IS_80386 Setng) = @{term "IS_80386 Setng"} 
|  mk_instr_mnemonic (IS_80386 Setnge) = @{term "IS_80386 Setnge"} |  mk_instr_mnemonic (IS_80386 Setnl) = @{term "IS_80386 Setnl"} |   mk_instr_mnemonic (IS_80386 Setnle) = @{term "IS_80386 Setnle"} |  mk_instr_mnemonic (IS_80386 Setno) = @{term "IS_80386 Setno"} |  mk_instr_mnemonic (IS_80386 Setnp) = @{term "IS_80386 Setnp"} |  mk_instr_mnemonic (IS_80386 Setns) = @{term "IS_80386 Setns"} 
|  mk_instr_mnemonic (IS_80386 Setnz) = @{term "IS_80386 Setnz"} |  mk_instr_mnemonic (IS_80386 Seto) = @{term "IS_80386 Seto"} |  mk_instr_mnemonic (IS_80386 Setp) = @{term "IS_80386 Setp"} |  mk_instr_mnemonic (IS_80386 Setpe) = @{term "IS_80386 Setpe"} |  mk_instr_mnemonic (IS_80386 Setpo) = @{term "IS_80386 Setpo"} |  mk_instr_mnemonic (IS_80386 Sets) = @{term "IS_80386 Sets"} 
|  mk_instr_mnemonic (IS_80386 Setz) = @{term "IS_80386 Setz"} |

  mk_instr_mnemonic (IS_80386_x87 Fcos) = @{term "IS_80386_x87 Fcos"} |  mk_instr_mnemonic (IS_80386_x87 Fldenvd) = @{term "IS_80386_x87 Fldenvd"} |  mk_instr_mnemonic (IS_80386_x87 Fsaved) = @{term "IS_80386_x87 Fsaved"} |  mk_instr_mnemonic (IS_80386_x87 Fstenvd) = @{term "IS_80386_x87 Fstenvd"} |  mk_instr_mnemonic (IS_80386_x87 Fprem1) = @{term "IS_80386_x87 Fprem1"} 
|  mk_instr_mnemonic (IS_80386_x87 Frstord) = @{term "IS_80386_x87 Frstord"} |  mk_instr_mnemonic (IS_80386_x87 Fsin) = @{term "IS_80386_x87 Fsin"} |  mk_instr_mnemonic (IS_80386_x87 Fsincos) = @{term "IS_80386_x87 Fsincos"} |  mk_instr_mnemonic (IS_80386_x87 Fucom) = @{term "IS_80386_x87 Fucom"} 
|  mk_instr_mnemonic (IS_80386_x87 Fucomp) = @{term "IS_80386_x87 Fucomp"} |  mk_instr_mnemonic (IS_80386_x87 Fucompp) = @{term "IS_80386_x87 Fucompp"} |

  mk_instr_mnemonic (IS_80486 Bswap) = @{term "IS_80486 Bswap"} |  mk_instr_mnemonic (IS_80486 Cmpxchg) = @{term "IS_80486 Cmpxchg"} |  mk_instr_mnemonic (IS_80486 Invd) = @{term "IS_80486 Invd"} |  mk_instr_mnemonic (IS_80486 Invlpg) = @{term "IS_80486 Invlpg"} |  mk_instr_mnemonic (IS_80486 Wbinvd) = @{term "IS_80486 Wbinvd"} |  mk_instr_mnemonic (IS_80486 Xadd) = @{term "IS_80486 Xadd"} |

  mk_instr_mnemonic (IS_Pentium Cpuid) = @{term "IS_Pentium Cpuid"} |  mk_instr_mnemonic (IS_Pentium Cmpxchg8b) = @{term "IS_Pentium Cmpxchg8b"} |  mk_instr_mnemonic (IS_Pentium Rdmsr) = @{term "IS_Pentium Rdmsr"} |  mk_instr_mnemonic (IS_Pentium Rdtsc) = @{term "IS_Pentium Rdtsc"} |  mk_instr_mnemonic (IS_Pentium Wrmsr) = @{term "IS_Pentium Wrmsr"} 
|  mk_instr_mnemonic (IS_Pentium Rsm) = @{term "IS_Pentium Rsm"} |

 mk_instr_mnemonic (IS_PentiumMMX Rdpmc) = @{term "IS_PentiumMMX Rdpmc"} |

  mk_instr_mnemonic (IS_PentiumMMX_MMX Emms) = @{term "IS_PentiumMMX_MMX Emms"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Movd) = @{term "IS_PentiumMMX_MMX Movd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Movq) = @{term "IS_PentiumMMX_MMX Movq"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Packssdw) = @{term "IS_PentiumMMX_MMX Packssdw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Packsswb) = @{term "IS_PentiumMMX_MMX Packsswb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Packuswb) = @{term "IS_PentiumMMX_MMX Packuswb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddb) = @{term "IS_PentiumMMX_MMX Paddb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddw) = @{term "IS_PentiumMMX_MMX Paddw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddd) = @{term "IS_PentiumMMX_MMX Paddd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddq) = @{term "IS_PentiumMMX_MMX Paddq"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddsb) = @{term "IS_PentiumMMX_MMX Paddsb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddsw) = @{term "IS_PentiumMMX_MMX Paddsw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddusb) = @{term "IS_PentiumMMX_MMX Paddusb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Paddusw) = @{term "IS_PentiumMMX_MMX Paddusw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pand) = @{term "IS_PentiumMMX_MMX Pand"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pandn) = @{term "IS_PentiumMMX_MMX Pandn"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Por) = @{term "IS_PentiumMMX_MMX Por"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pxor) = @{term "IS_PentiumMMX_MMX Pxor"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqb) = @{term "IS_PentiumMMX_MMX Pcmpeqb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqw) = @{term "IS_PentiumMMX_MMX Pcmpeqw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqd) = @{term "IS_PentiumMMX_MMX Pcmpeqd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtb) = @{term "IS_PentiumMMX_MMX Pcmpgtb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtw) = @{term "IS_PentiumMMX_MMX Pcmpgtw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtd) = @{term "IS_PentiumMMX_MMX Pcmpgtd"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Pmaddwd) = @{term "IS_PentiumMMX_MMX Pmaddwd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pmulhw) = @{term "IS_PentiumMMX_MMX Pmulhw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Pmullw) = @{term "IS_PentiumMMX_MMX Pmullw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psllw) = @{term "IS_PentiumMMX_MMX Psllw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Pslld) = @{term "IS_PentiumMMX_MMX Pslld"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psllq) = @{term "IS_PentiumMMX_MMX Psllq"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psrad) = @{term "IS_PentiumMMX_MMX Psrad"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psraw) = @{term "IS_PentiumMMX_MMX Psraw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Psrlw) = @{term "IS_PentiumMMX_MMX Psrlw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psrld) = @{term "IS_PentiumMMX_MMX Psrld"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psrlq) = @{term "IS_PentiumMMX_MMX Psrlq"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubb) = @{term "IS_PentiumMMX_MMX Psubb"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubw) = @{term "IS_PentiumMMX_MMX Psubw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubd) = @{term "IS_PentiumMMX_MMX Psubd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubsb) = @{term "IS_PentiumMMX_MMX Psubsb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubsw) = @{term "IS_PentiumMMX_MMX Psubsw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubusb) = @{term "IS_PentiumMMX_MMX Psubusb"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Psubusw) = @{term "IS_PentiumMMX_MMX Psubusw"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Punpckhbw) = @{term "IS_PentiumMMX_MMX Punpckhbw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Punpckhwd) = @{term "IS_PentiumMMX_MMX Punpckhwd"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Punpckhdq) = @{term "IS_PentiumMMX_MMX Punpckhdq"} |  mk_instr_mnemonic (IS_PentiumMMX_MMX Punpcklbw) = @{term "IS_PentiumMMX_MMX Punpcklbw"} 
|  mk_instr_mnemonic (IS_PentiumMMX_MMX Punpcklwd) = @{term "IS_PentiumMMX_MMX Punpcklwd"} |   mk_instr_mnemonic (IS_PentiumMMX_MMX Punpckldq) = @{term "IS_PentiumMMX_MMX Punpckldq"} |

  mk_instr_mnemonic (IS_PentiumPro Cmova) = @{term "IS_PentiumPro Cmova"} |  mk_instr_mnemonic (IS_PentiumPro Cmovae) = @{term "IS_PentiumPro Cmovae"} |  mk_instr_mnemonic (IS_PentiumPro Cmovb) = @{term "IS_PentiumPro Cmovb"} |  mk_instr_mnemonic (IS_PentiumPro Cmovbe) = @{term "IS_PentiumPro Cmovbe"} |  mk_instr_mnemonic (IS_PentiumPro Cmovc) = @{term "IS_PentiumPro Cmovc"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmove) = @{term "IS_PentiumPro Cmove"} |  mk_instr_mnemonic (IS_PentiumPro Cmovg) = @{term "IS_PentiumPro Cmovg"} |  mk_instr_mnemonic (IS_PentiumPro Cmovge) = @{term "IS_PentiumPro Cmovge"} |  mk_instr_mnemonic (IS_PentiumPro Cmovl) = @{term "IS_PentiumPro Cmovl"} |  mk_instr_mnemonic (IS_PentiumPro Cmovle) = @{term "IS_PentiumPro Cmovle"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmovna) = @{term "IS_PentiumPro Cmovna"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnae) = @{term "IS_PentiumPro Cmovnae"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnb) = @{term "IS_PentiumPro Cmovnb"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnbe) = @{term "IS_PentiumPro Cmovnbe"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmovnc) = @{term "IS_PentiumPro Cmovnc"} |  mk_instr_mnemonic (IS_PentiumPro Cmovne) = @{term "IS_PentiumPro Cmovne"} |   mk_instr_mnemonic (IS_PentiumPro Cmovng) = @{term "IS_PentiumPro Cmovng"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnge) = @{term "IS_PentiumPro Cmovnge"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmovnl) = @{term "IS_PentiumPro Cmovnl"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnle) = @{term "IS_PentiumPro Cmovnle"} |  mk_instr_mnemonic (IS_PentiumPro Cmovno) = @{term "IS_PentiumPro Cmovno"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnp) = @{term "IS_PentiumPro Cmovnp"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmovns) = @{term "IS_PentiumPro Cmovns"} |  mk_instr_mnemonic (IS_PentiumPro Cmovnz) = @{term "IS_PentiumPro Cmovnz"} |  mk_instr_mnemonic (IS_PentiumPro Cmovo) = @{term "IS_PentiumPro Cmovo"} |  mk_instr_mnemonic (IS_PentiumPro Cmovp) = @{term "IS_PentiumPro Cmovp"} 
|  mk_instr_mnemonic (IS_PentiumPro Cmovpe) = @{term "IS_PentiumPro Cmovpe"} |  mk_instr_mnemonic (IS_PentiumPro Cmovpo) = @{term "IS_PentiumPro Cmovpo"} |  mk_instr_mnemonic (IS_PentiumPro Cmovs) = @{term "IS_PentiumPro Cmovs"} |  mk_instr_mnemonic (IS_PentiumPro Cmovz) = @{term "IS_PentiumPro Cmovz"} |  mk_instr_mnemonic (IS_PentiumPro Ud2) = @{term "IS_PentiumPro Ud2"} |

  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovb) = @{term "IS_PentiumPro_x87 Fcmovb"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovbe) = @{term "IS_PentiumPro_x87 Fcmovbe"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmove) = @{term "IS_PentiumPro_x87 Fcmove"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovnb) = @{term "IS_PentiumPro_x87 Fcmovnb"} 
|  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovnbe) = @{term "IS_PentiumPro_x87 Fcmovnbe"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovne) = @{term "IS_PentiumPro_x87 Fcmovne"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovnu) = @{term "IS_PentiumPro_x87 Fcmovnu"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcmovu) = @{term "IS_PentiumPro_x87 Fcmovu"} 
|  mk_instr_mnemonic (IS_PentiumPro_x87 Fcomi) = @{term "IS_PentiumPro_x87 Fcomi"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fcomip) = @{term "IS_PentiumPro_x87 Fcomip"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fucomi) = @{term "IS_PentiumPro_x87 Fucomi"} |  mk_instr_mnemonic (IS_PentiumPro_x87 Fucomip) = @{term "IS_PentiumPro_x87 Fucomip"} |

  mk_instr_mnemonic (IS_PentiumII Sysenter) = @{term "IS_PentiumII Sysenter"} |  mk_instr_mnemonic (IS_PentiumII Sysexit) = @{term "IS_PentiumII Sysexit"} |

  mk_instr_mnemonic (IS_SSE Maskmovq) = @{term "IS_SSE Maskmovq"} |  mk_instr_mnemonic (IS_SSE Movntq) = @{term "IS_SSE Movntq"} |  mk_instr_mnemonic (IS_SSE Prefetcht0) = @{term "IS_SSE Prefetcht0"} |  mk_instr_mnemonic (IS_SSE Prefetcht1) = @{term "IS_SSE Prefetcht1"} 
|  mk_instr_mnemonic (IS_SSE Prefetcht2) = @{term "IS_SSE Prefetcht2"} |  mk_instr_mnemonic (IS_SSE Prefetchnta) = @{term "IS_SSE Prefetchnta"} |  mk_instr_mnemonic (IS_SSE Sfence) = @{term "IS_SSE Sfence"} |

  mk_instr_mnemonic (IS_SSE_x87 Fxrstor) = @{term "IS_SSE_x87 Fxrstor"} |  mk_instr_mnemonic (IS_SSE_x87 Fxsave) = @{term "IS_SSE_x87 Fxsave"} |

  mk_instr_mnemonic (IS_SSE_SIMDMMX Pshufw) = @{term "IS_SSE_SIMDMMX Pshufw"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pinsrw) = @{term "IS_SSE_SIMDMMX Pinsrw"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pextrw) = @{term "IS_SSE_SIMDMMX Pextrw"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pmovmskb) = @{term "IS_SSE_SIMDMMX Pmovmskb"} 
|  mk_instr_mnemonic (IS_SSE_SIMDMMX Pminub) = @{term "IS_SSE_SIMDMMX Pminub"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pmaxub) = @{term "IS_SSE_SIMDMMX Pmaxub"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pavgb) = @{term "IS_SSE_SIMDMMX Pavgb"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pavgw) = @{term "IS_SSE_SIMDMMX Pavgw"} 
|  mk_instr_mnemonic (IS_SSE_SIMDMMX Pmulhuw) = @{term "IS_SSE_SIMDMMX Pmulhuw"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pminsw) = @{term "IS_SSE_SIMDMMX Pminsw"} |  mk_instr_mnemonic (IS_SSE_SIMDMMX Pmaxsw) = @{term "IS_SSE_SIMDMMX Pmaxsw"} 
|  mk_instr_mnemonic (IS_SSE_SIMDMMX Psadbw) = @{term "IS_SSE_SIMDMMX Psadbw"} |

mk_instr_mnemonic (IS_SSE_SIMD Andps) = @{term "IS_SSE_SIMD Andps"} |  mk_instr_mnemonic (IS_SSE_SIMD Andnps) = @{term "IS_SSE_SIMD Andnps"} |  mk_instr_mnemonic (IS_SSE_SIMD Orps) = @{term "IS_SSE_SIMD Orps"} |  mk_instr_mnemonic (IS_SSE_SIMD Xorps) = @{term "IS_SSE_SIMD Xorps"} |  mk_instr_mnemonic (IS_SSE_SIMD Movups) = @{term "IS_SSE_SIMD Movups"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Movss) = @{term "IS_SSE_SIMD Movss"} |  mk_instr_mnemonic (IS_SSE_SIMD Movhlps) = @{term "IS_SSE_SIMD Movhlps"} |  mk_instr_mnemonic (IS_SSE_SIMD Movlps) = @{term "IS_SSE_SIMD Movlps"} |  mk_instr_mnemonic (IS_SSE_SIMD Unpcklps) = @{term "IS_SSE_SIMD Unpcklps"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Unpckhps) = @{term "IS_SSE_SIMD Unpckhps"} |  mk_instr_mnemonic (IS_SSE_SIMD Movlhps) = @{term "IS_SSE_SIMD Movlhps"} |  mk_instr_mnemonic (IS_SSE_SIMD Movhps) = @{term "IS_SSE_SIMD Movhps"} |  mk_instr_mnemonic (IS_SSE_SIMD Movaps) = @{term "IS_SSE_SIMD Movaps"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Movmskps) = @{term "IS_SSE_SIMD Movmskps"} |  mk_instr_mnemonic (IS_SSE_SIMD Cvtpi2ps) = @{term "IS_SSE_SIMD Cvtpi2ps"} |  mk_instr_mnemonic (IS_SSE_SIMD Cvtsi2ss) = @{term "IS_SSE_SIMD Cvtsi2ss"} |  mk_instr_mnemonic (IS_SSE_SIMD Movntps) = @{term "IS_SSE_SIMD Movntps"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Cvttps2pi) = @{term "IS_SSE_SIMD Cvttps2pi"} |  mk_instr_mnemonic (IS_SSE_SIMD Cvttss2si) = @{term "IS_SSE_SIMD Cvttss2si"} |   mk_instr_mnemonic (IS_SSE_SIMD Cvtps2pi) = @{term "IS_SSE_SIMD Cvtps2pi"} |  mk_instr_mnemonic (IS_SSE_SIMD Cvtss2si) = @{term "IS_SSE_SIMD Cvtss2si"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Ucomiss) = @{term "IS_SSE_SIMD Ucomiss"} |  mk_instr_mnemonic (IS_SSE_SIMD Comiss) = @{term "IS_SSE_SIMD Comiss"} |  mk_instr_mnemonic (IS_SSE_SIMD Sqrtps) = @{term "IS_SSE_SIMD Sqrtps"} |  mk_instr_mnemonic (IS_SSE_SIMD Sqrtss) = @{term "IS_SSE_SIMD Sqrtss"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Rsqrtps) = @{term "IS_SSE_SIMD Rsqrtps"} |  mk_instr_mnemonic (IS_SSE_SIMD Rsqrtss) = @{term "IS_SSE_SIMD Rsqrtss"} |  mk_instr_mnemonic (IS_SSE_SIMD Rcpps) = @{term "IS_SSE_SIMD Rcpps"} |  mk_instr_mnemonic (IS_SSE_SIMD Rcpss) = @{term "IS_SSE_SIMD Rcpss"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Addps) = @{term "IS_SSE_SIMD Addps"} |  mk_instr_mnemonic (IS_SSE_SIMD Addss) = @{term "IS_SSE_SIMD Addss"} |  mk_instr_mnemonic (IS_SSE_SIMD Mulps) = @{term "IS_SSE_SIMD Mulps"} |  mk_instr_mnemonic (IS_SSE_SIMD Mulss) = @{term "IS_SSE_SIMD Mulss"} |  mk_instr_mnemonic (IS_SSE_SIMD Subps) = @{term "IS_SSE_SIMD Subps"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Subss) = @{term "IS_SSE_SIMD Subss"} |   mk_instr_mnemonic (IS_SSE_SIMD Minps) = @{term "IS_SSE_SIMD Minps"} |  mk_instr_mnemonic (IS_SSE_SIMD Minss) = @{term "IS_SSE_SIMD Minss"} |  mk_instr_mnemonic (IS_SSE_SIMD Divps) = @{term "IS_SSE_SIMD Divps"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Divss) = @{term "IS_SSE_SIMD Divss"} |  mk_instr_mnemonic (IS_SSE_SIMD Maxps) = @{term "IS_SSE_SIMD Maxps"} |  mk_instr_mnemonic (IS_SSE_SIMD Maxss) = @{term "IS_SSE_SIMD Maxss"} |  mk_instr_mnemonic (IS_SSE_SIMD Ldmxcsr) = @{term "IS_SSE_SIMD Ldmxcsr"} 
|  mk_instr_mnemonic (IS_SSE_SIMD Stmxcsr) = @{term "IS_SSE_SIMD Stmxcsr"} |  mk_instr_mnemonic (IS_SSE_SIMD Cmpps) = @{term "IS_SSE_SIMD Cmpps"} |  mk_instr_mnemonic (IS_SSE_SIMD Cmpss) = @{term "IS_SSE_SIMD Cmpss"} |  mk_instr_mnemonic (IS_SSE_SIMD Shufps) = @{term "IS_SSE_SIMD Shufps"} |

  mk_instr_mnemonic (IS_SSE2 Clflush) = @{term "IS_SSE2 Clflush"} |  mk_instr_mnemonic (IS_SSE2 Lfence) = @{term "IS_SSE_SIMD Lfence"} |  mk_instr_mnemonic (IS_SSE2 Mfence) = @{term "IS_SSE2 Mfence"} |  mk_instr_mnemonic (IS_SSE2 Movnti) = @{term "IS_SSE2 Movnti"} |  mk_instr_mnemonic (IS_SSE2 Pause) = @{term "IS_SSE2 Pause"} |

  mk_instr_mnemonic (IS_SSE2_SIMDMMX Psubq) = @{term "IS_SSE2_SIMDMMX Psubq"} |  mk_instr_mnemonic (IS_SSE2_SIMDMMX Pmuludq) = @{term "IS_SSE2_SIMDMMX Pmuludq"} |

  mk_instr_mnemonic (IS_SSE2_SIMD Movapd) = @{term "IS_SSE2_SIMD Movapd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movntpd) = @{term "IS_SSE2_SIMD Movntpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movhpd) = @{term "IS_SSE2_SIMD Movhpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movlpd) = @{term "IS_SSE2_SIMD Movlpd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Movupd) = @{term "IS_SSE2_SIMD Movupd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movmskpd) = @{term "IS_SSE2_SIMD Movmskpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movsd) = @{term "IS_SSE2_SIMD Movsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Addpd) = @{term "IS_SSE2_SIMD Addpd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Addsd) = @{term "IS_SSE2_SIMD Addsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Divpd) = @{term "IS_SSE2_SIMD Divpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Divsd) = @{term "IS_SSE2_SIMD Divsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Maxpd) = @{term "IS_SSE2_SIMD Maxpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Maxsd) = @{term "IS_SSE2_SIMD Maxsd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Minpd) = @{term "IS_SSE2_SIMD Minpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Minsd) = @{term "IS_SSE2_SIMD Minsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Mulpd) = @{term "IS_SSE2_SIMD Mulpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Mulsd) = @{term "IS_SSE2_SIMD Mulsd"} |   mk_instr_mnemonic (IS_SSE2_SIMD Sqrtpd) = @{term "IS_SSE2_SIMD Sqrtpd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Sqrtsd) = @{term "IS_SSE2_SIMD Sqrtsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Subpd) = @{term "IS_SSE2_SIMD Subpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Subsd) = @{term "IS_SSE2_SIMD Subsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Andpd) = @{term "IS_SSE2_SIMD Andpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Andnpd) = @{term "IS_SSE2_SIMD Andnpd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Orpd) = @{term "IS_SSE2_SIMD Orpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Xorpd) = @{term "IS_SSE2_SIMD Xorpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cmppd) = @{term "IS_SSE2_SIMD Cmppd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cmpsd) = @{term "IS_SSE2_SIMD Cmpsd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Comisd) = @{term "IS_SSE2_SIMD Comisd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Ucomisd) = @{term "IS_SSE2_SIMD Ucomisd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Shufpd) = @{term "IS_SSE2_SIMD Shufpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Unpckhpd) = @{term "IS_SSE2_SIMD Unpckhpd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Unpcklpd) = @{term "IS_SSE2_SIMD Unpcklpd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Cvtdq2pd) = @{term "IS_SSE2_SIMD Cvtdq2pd"} |   mk_instr_mnemonic (IS_SSE2_SIMD Cvtdq2ps) = @{term "IS_SSE2_SIMD Cvtdq2ps"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtpd2dq) = @{term "IS_SSE2_SIMD Cvtpd2dq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtpd2pi) = @{term "IS_SSE2_SIMD Cvtpd2pi"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Cvtpd2ps) = @{term "IS_SSE2_SIMD Cvtpd2ps"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtpi2pd) = @{term "IS_SSE2_SIMD Cvtpi2pd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtps2dq) = @{term "IS_SSE2_SIMD Cvtps2dq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtps2pd) = @{term "IS_SSE2_SIMD Cvtps2pd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Cvtsd2si) = @{term "IS_SSE2_SIMD Cvtsd2si"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtsd2ss) = @{term "IS_SSE2_SIMD Cvtsd2ss"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtsi2sd) = @{term "IS_SSE2_SIMD Cvtsi2sd"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvtss2sd) = @{term "IS_SSE2_SIMD Cvtss2sd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Cvttpd2dq) = @{term "IS_SSE2_SIMD Cvttpd2dq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvttpd2pi) = @{term "IS_SSE2_SIMD Cvttpd2pi"} |   mk_instr_mnemonic (IS_SSE2_SIMD Cvttps2dq) = @{term "IS_SSE2_SIMD Cvttps2dq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Cvttsd2si) = @{term "IS_SSE2_SIMD Cvttsd2si"}   
|  mk_instr_mnemonic (IS_SSE2_SIMD Maskmovdqu) = @{term "IS_SSE2_SIMD Maskmovdqu"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Movdq2q) = @{term "IS_SSE2_SIMD Movdq2q"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movdqa) = @{term "IS_SSE2_SIMD Movdqa"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movdqu) = @{term "IS_SSE2_SIMD Movdqu"} |  mk_instr_mnemonic (IS_SSE2_SIMD Movq2dq) = @{term "IS_SSE2_SIMD Movq2dq"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Movntdq) = @{term "IS_SSE2_SIMD Movntdq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Pshufhw) = @{term "IS_SSE2_SIMD Pshufhw"} |  mk_instr_mnemonic (IS_SSE2_SIMD Pshuflw) = @{term "IS_SSE2_SIMD Pshuflw"} |  mk_instr_mnemonic (IS_SSE2_SIMD Pshufd) = @{term "IS_SSE2_SIMD Pshufd"} 
|  mk_instr_mnemonic (IS_SSE2_SIMD Pslldq) = @{term "IS_SSE2_SIMD Pslldq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Psrldq) = @{term "IS_SSE2_SIMD Psrldq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Punpckhqdq) = @{term "IS_SSE2_SIMD Punpckhqdq"} |  mk_instr_mnemonic (IS_SSE2_SIMD Punpcklqdq) = @{term "IS_SSE2_SIMD Punpcklqdq"} |

  mk_instr_mnemonic (IS_X86_64 Cdqe) = @{term "IS_X86_64 Cdqe"} |  mk_instr_mnemonic (IS_X86_64 Cqo) = @{term "IS_X86_64 Cqo"} |  mk_instr_mnemonic (IS_X86_64 Cmpsq) = @{term "IS_X86_64 Cmpsq"} |  mk_instr_mnemonic (IS_X86_64 Cmpxchg16b) = @{term "IS_X86_64 Cmpxchg16b"} |  mk_instr_mnemonic (IS_X86_64 Iretq) = @{term "IS_X86_64 Iretq"} 
|  mk_instr_mnemonic (IS_X86_64 Jrcxz) = @{term "IS_X86_64 Jrcxz"} |  mk_instr_mnemonic (IS_X86_64 Lodsq) = @{term "IS_X86_64 Lodsq"} |  mk_instr_mnemonic (IS_X86_64 Movsxd) = @{term "IS_X86_64 Movsxd"} |  mk_instr_mnemonic (IS_X86_64 Popfq) = @{term "IS_X86_64 Popfq"} |  mk_instr_mnemonic (IS_X86_64 Pushfq) = @{term "IS_X86_64 Pushfq"} 
|  mk_instr_mnemonic (IS_X86_64 Rdtscp) = @{term "IS_X86_64 Rdtscp"} |  mk_instr_mnemonic (IS_X86_64 Scasq) = @{term "IS_X86_64 Scasq"} |  mk_instr_mnemonic (IS_X86_64 Stosq) = @{term "IS_X86_64 Stosq"} |  mk_instr_mnemonic (IS_X86_64 Swapgs) = @{term "IS_X86_64 Swapgs"} |

  mk_instr_mnemonic (IS_SSE3 Monitor) = @{term "IS_SSE3 Monitor"} |  mk_instr_mnemonic (IS_SSE3 Mwait) = @{term "IS_SSE3 Mwait"} |

  mk_instr_mnemonic (IS_SSE3_x87 Fisttp) = @{term "IS_SSE3_x87 Fisttp"} |

  mk_instr_mnemonic (IS_SSE3_SIMD Addsubps) = @{term "IS_SSE3_SIMD Addsubps"} |  mk_instr_mnemonic (IS_SSE3_SIMD Addsubpd) = @{term "IS_SSE3_SIMD Addsubpd"} |  mk_instr_mnemonic (IS_SSE3_SIMD Movddup) = @{term "IS_SSE3_SIMD Movddup"} |  mk_instr_mnemonic (IS_SSE3_SIMD Movsldup) = @{term "IS_SSE3_SIMD Movsldup"} 
|  mk_instr_mnemonic (IS_SSE3_SIMD Movshdup) = @{term "IS_SSE3_SIMD Movshdup"} |  mk_instr_mnemonic (IS_SSE3_SIMD Haddps) = @{term "IS_SSE3_SIMD Haddps"} |  mk_instr_mnemonic (IS_SSE3_SIMD Haddpd) = @{term "IS_SSE3_SIMD Haddpd"} |  mk_instr_mnemonic (IS_SSE3_SIMD Hsubps) = @{term "IS_SSE3_SIMD Hsubps"} 
|  mk_instr_mnemonic (IS_SSE3_SIMD Hsubpd) = @{term "IS_SSE3_SIMD Hsubpd"} |  mk_instr_mnemonic (IS_SSE3_SIMD Lddqu) = @{term "IS_SSE3_SIMD Lddqu"} |

  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Psignb) = @{term "IS_SSSE3_SIMDMMX Psignb"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Psignw) = @{term "IS_SSSE3_SIMDMMX Psignw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Psignd) = @{term "IS_SSSE3_SIMDMMX Psignd"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pshufb) = @{term "IS_SSSE3_SIMDMMX Pshufb"} 
|  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pmulhrsw) = @{term "IS_SSSE3_SIMDMMX Pmulhrsw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pmaddubsw) = @{term "IS_SSSE3_SIMDMMX Pmaddubsw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubw) = @{term "IS_SSSE3_SIMDMMX Phsubw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubsw) = @{term "IS_SSSE3_SIMDMMX Phsubsw"} 
|  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubd) = @{term "IS_SSSE3_SIMDMMX Phsubd"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddsw) = @{term "IS_SSSE3_SIMDMMX Phaddsw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddw) = @{term "IS_SSSE3_SIMDMMX Phaddw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddd) = @{term "IS_SSSE3_SIMDMMX Phaddd"} 
|  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Palignr) = @{term "IS_SSSE3_SIMDMMX Palignr"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsb) = @{term "IS_SSSE3_SIMDMMX Pabsb"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsw) = @{term "IS_SSSE3_SIMDMMX Pabsw"} |  mk_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsd) = @{term "IS_SSSE3_SIMDMMX Pabsd"} |

  mk_instr_mnemonic (IS_SSE4_1_SIMD Dpps) = @{term "IS_SSE4_1_SIMD Dpps"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Dppd) = @{term "IS_SSE4_1_SIMD Dppd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Blendps) = @{term "IS_SSE4_1_SIMD Blendps"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Blendvps) = @{term "IS_SSE4_1_SIMD Blendvps"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Blendpd) = @{term "IS_SSE4_1_SIMD Blendpd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Blendvpd) = @{term "IS_SSE4_1_SIMD Blendvpd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Roundps) = @{term "IS_SSE4_1_SIMD Roundps"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Roundss) = @{term "IS_SSE4_1_SIMD Roundss"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Roundpd) = @{term "IS_SSE4_1_SIMD Roundpd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Roundsd) = @{term "IS_SSE4_1_SIMD Roundsd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Insertps) = @{term "IS_SSE4_1_SIMD Insertps"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Extractps) = @{term "IS_SSE4_1_SIMD Extractps"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Mpsadbw) = @{term "IS_SSE4_1_SIMD Mpsadbw"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Phminposuw) = @{term "IS_SSE4_1_SIMD Phminposuw"} |   mk_instr_mnemonic (IS_SSE4_1_SIMD Pmulld) = @{term "IS_SSE4_1_SIMD Pmulld"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmuldq) = @{term "IS_SSE4_1_SIMD Pmuldq"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pblendvb) = @{term "IS_SSE4_1_SIMD Pblendvb"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pblendw) = @{term "IS_SSE4_1_SIMD Pblendw"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pminsb) = @{term "IS_SSE4_1_SIMD Pminsb"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pminuw) = @{term "IS_SSE4_1_SIMD Pminuw"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pminsd) = @{term "IS_SSE4_1_SIMD Pminsd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pminud) = @{term "IS_SSE4_1_SIMD Pminud"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmaxsb) = @{term "IS_SSE4_1_SIMD Pmaxsb"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmaxuw) = @{term "IS_SSE4_1_SIMD Pmaxuw"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmaxsd) = @{term "IS_SSE4_1_SIMD Pmaxsd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmaxud) = @{term "IS_SSE4_1_SIMD Pmaxud"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pinsrb) = @{term "IS_SSE4_1_SIMD Pinsrb"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pinsrd) = @{term "IS_SSE4_1_SIMD Pinsrd"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pinsrq) = @{term "IS_SSE4_1_SIMD Pinsrq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pextrb) = @{term "IS_SSE4_1_SIMD Pextrb"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pextrd) = @{term "IS_SSE4_1_SIMD Pextrd"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pextrq) = @{term "IS_SSE4_1_SIMD Pextrq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbw) = @{term "IS_SSE4_1_SIMD Pmovsxbw"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbw) = @{term "IS_SSE4_1_SIMD Pmovzxbw"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbd) = @{term "IS_SSE4_1_SIMD Pmovsxbd"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbd) = @{term "IS_SSE4_1_SIMD Pmovzxbd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbq) = @{term "IS_SSE4_1_SIMD Pmovsxbq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbq) = @{term "IS_SSE4_1_SIMD Pmovzxbq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxwd) = @{term "IS_SSE4_1_SIMD Pmovsxwd"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxwd) = @{term "IS_SSE4_1_SIMD Pmovzxwd"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxwq) = @{term "IS_SSE4_1_SIMD Pmovsxwq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxwq) = @{term "IS_SSE4_1_SIMD Pmovzxwq"} |   mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxdq) = @{term "IS_SSE4_1_SIMD Pmovsxdq"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxdq) = @{term "IS_SSE4_1_SIMD Pmovzxdq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Ptest) = @{term "IS_SSE4_1_SIMD Ptest"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Pcmpeqq) = @{term "IS_SSE4_1_SIMD Pcmpeqq"} |  mk_instr_mnemonic (IS_SSE4_1_SIMD Packusdw) = @{term "IS_SSE4_1_SIMD Packusdw"} 
|  mk_instr_mnemonic (IS_SSE4_1_SIMD Movntdqa) = @{term "IS_SSE4_1_SIMD Movntdqa"} |

  mk_instr_mnemonic (IS_VT_X Vmptrld) = @{term "IS_VT_X Vmptrld"} |  mk_instr_mnemonic (IS_VT_X Vmptrst) = @{term "IS_VT_X Vmptrst"} |  mk_instr_mnemonic (IS_VT_X Vmclear) = @{term "IS_VT_X Vmclear"} |  mk_instr_mnemonic (IS_VT_X Vmread) = @{term "IS_VT_X Vmread"} |  mk_instr_mnemonic (IS_VT_X Vmwrite) = @{term "IS_VT_X Vmwrite"} 
|  mk_instr_mnemonic (IS_VT_X Vmcall) = @{term "IS_VT_X Vmcall"} |  mk_instr_mnemonic (IS_VT_X Vmlaunch) = @{term "IS_VT_X Vmlaunch"} |  mk_instr_mnemonic (IS_VT_X Vmresume) = @{term "IS_VT_X Vmresume"} |  mk_instr_mnemonic (IS_VT_X Vmxoff) = @{term "IS_VT_X Vmxoff"} |  mk_instr_mnemonic (IS_VT_X Vmxon) = @{term "IS_VT_X Vmxon"} 
|  mk_instr_mnemonic (IS_VT_X Vmfunc) = @{term "IS_VT_X Vmfunc"} |  mk_instr_mnemonic (IS_VT_X Invvpid) = @{term "IS_VT_X Invvpid"} |  mk_instr_mnemonic (IS_VT_X Invvpid) = @{term "IS_VT_X Invvpid"} |

  mk_instr_mnemonic (IS_SSE4_2 Crc32) = @{term "IS_SSE4_2 Crc32"} |  mk_instr_mnemonic (IS_SSE4_2 Popcnt) = @{term "IS_SSE4_2 Popcnt"} |

  mk_instr_mnemonic (IS_SSE4_2_SIMD Pcmpestri) = @{term "IS_SSE4_2_SIMD Pcmpestri"} |  mk_instr_mnemonic (IS_SSE4_2_SIMD Pcmpestrm) = @{term "IS_SSE4_2_SIMD Pcmpestrm"} |  mk_instr_mnemonic (IS_SSE4_2_SIMD Pcmpistri) = @{term "IS_SSE4_2_SIMD Pcmpistri"} |  mk_instr_mnemonic (IS_SSE4_2_SIMD Pcmpistrm) = @{term "IS_SSE4_2_SIMD Pcmpistrm"} 
|  mk_instr_mnemonic (IS_SSE4_2_SIMD Pcmpgtq) = @{term "IS_SSE4_2_SIMD Pcmpgtq"} |

  mk_instr_mnemonic (IS_AVX Vsqrtps) = @{term "IS_AVX Vsqrtps"} |  mk_instr_mnemonic (IS_AVX Vsqrtpd) = @{term "IS_AVX Vsqrtpd"} |  mk_instr_mnemonic (IS_AVX Vrsqrtps) = @{term "IS_AVX Vrsqrtps"} |  mk_instr_mnemonic (IS_AVX Vrcpps) = @{term "IS_AVX Vrcpps"} |  mk_instr_mnemonic (IS_AVX Vaddps) = @{term "IS_AVX Vaddps"} 
|  mk_instr_mnemonic (IS_AVX Vaddpd) = @{term "IS_AVX Vaddpd"} |  mk_instr_mnemonic (IS_AVX Vsubps) = @{term "IS_AVX Vsubps"} |  mk_instr_mnemonic (IS_AVX Vsubpd) = @{term "IS_AVX Vsubpd"} |  mk_instr_mnemonic (IS_AVX Vmulps) = @{term "IS_AVX Vmulps"} |  mk_instr_mnemonic (IS_AVX Vmulpd) = @{term "IS_AVX Vmulpd"} 
|  mk_instr_mnemonic (IS_AVX Vdivps) = @{term "IS_AVX Vdivps"} |  mk_instr_mnemonic (IS_AVX Vdivpd) = @{term "IS_AVX Vdivpd"} |  mk_instr_mnemonic (IS_AVX Vcvtps2pd) = @{term "IS_AVX Vcvtps2pd"} |  mk_instr_mnemonic (IS_AVX Vcvtpd2ps) = @{term "IS_AVX Vcvtpd2ps"} |  mk_instr_mnemonic (IS_AVX Vcvtdq2ps) = @{term "IS_AVX Vcvtdq2ps"} 
|  mk_instr_mnemonic (IS_AVX Vcvtps2dq) = @{term "IS_AVX Vcvtps2dq"} |  mk_instr_mnemonic (IS_AVX Vcvttps2dq) = @{term "IS_AVX Vcvttps2dq"} |  mk_instr_mnemonic (IS_AVX Vcvttpd2dq) = @{term "IS_AVX Vcvttpd2dq"} |  mk_instr_mnemonic (IS_AVX Vcvtpd2dq) = @{term "IS_AVX Vcvtpd2dq"} 
|  mk_instr_mnemonic (IS_AVX Vcvtdq2pd) = @{term "IS_AVX Vcvtdq2pd"} |  mk_instr_mnemonic (IS_AVX Vminps) = @{term "IS_AVX Vminps"} |  mk_instr_mnemonic (IS_AVX Vminpd) = @{term "IS_AVX Vminpd"} |  mk_instr_mnemonic (IS_AVX Vmaxps) = @{term "IS_AVX Vmaxps"} |  mk_instr_mnemonic (IS_AVX Vmaxpd) = @{term "IS_AVX Vmaxpd"} 
|  mk_instr_mnemonic (IS_AVX Vhaddpd) = @{term "IS_AVX Vhaddpd"} |  mk_instr_mnemonic (IS_AVX Vhaddps) = @{term "IS_AVX Vhaddps"} |  mk_instr_mnemonic (IS_AVX Vhsubpd) = @{term "IS_AVX Vhsubpd"} |  mk_instr_mnemonic (IS_AVX Vhsubps) = @{term "IS_AVX Vhsubps"} |  mk_instr_mnemonic (IS_AVX Vcmpps) = @{term "IS_AVX Vcmpps"} 
|  mk_instr_mnemonic (IS_AVX Vcmppd) = @{term "IS_AVX Vcmppd"} |  mk_instr_mnemonic (IS_AVX Vaddsubpd) = @{term "IS_AVX Vaddsubpd"} |  mk_instr_mnemonic (IS_AVX Vaddsubps) = @{term "IS_AVX Vaddsubps"} |  mk_instr_mnemonic (IS_AVX Vdpps) = @{term "IS_AVX Vdpps"} |  mk_instr_mnemonic (IS_AVX Vroundpd) = @{term "IS_AVX Vroundpd"} 
|  mk_instr_mnemonic (IS_AVX Vroundps) = @{term "IS_AVX Vroundps"} |  mk_instr_mnemonic (IS_AVX Vmovaps) = @{term "IS_AVX Vmovaps"} |  mk_instr_mnemonic (IS_AVX Vmovapd) = @{term "IS_AVX Vmovapd"} |  mk_instr_mnemonic (IS_AVX Vmovdqa) = @{term "IS_AVX Vmovdqa"} |  mk_instr_mnemonic (IS_AVX Vmovups) = @{term "IS_AVX Vmovups"} 
|  mk_instr_mnemonic (IS_AVX Vmovupd) = @{term "IS_AVX Vmovupd"} |  mk_instr_mnemonic (IS_AVX Vmovdqu) = @{term "IS_AVX Vmovdqu"} |  mk_instr_mnemonic (IS_AVX Vmovmskps) = @{term "IS_AVX Vmovmskps"} |  mk_instr_mnemonic (IS_AVX Vmovmskpd) = @{term "IS_AVX Vmovmskpd"} |   mk_instr_mnemonic (IS_AVX Vlddqu) = @{term "IS_AVX Vlddqu"} 
|  mk_instr_mnemonic (IS_AVX Vmovntps) = @{term "IS_AVX Vmovntps"} |  mk_instr_mnemonic (IS_AVX Vmovntpd) = @{term "IS_AVX Vmovntpd"} |  mk_instr_mnemonic (IS_AVX Vmovntdq) = @{term "IS_AVX Vmovntdq"} |  mk_instr_mnemonic (IS_AVX Vmovntdqa) = @{term "IS_AVX Vmovntdqa"} |  mk_instr_mnemonic (IS_AVX Vmovshdup) = @{term "IS_AVX Vmovshdup"} 
|  mk_instr_mnemonic (IS_AVX Vmovsldup) = @{term "IS_AVX Vmovsldup"} |  mk_instr_mnemonic (IS_AVX Vmovddup) = @{term "IS_AVX Vmovddup"} |  mk_instr_mnemonic (IS_AVX Vunpckhpd) = @{term "IS_AVX Vunpckhpd"} |  mk_instr_mnemonic (IS_AVX Vunpckhps) = @{term "IS_AVX Vunpckhps"} |  mk_instr_mnemonic (IS_AVX Vunpcklpd) = @{term "IS_AVX Vunpcklpd"} 
|  mk_instr_mnemonic (IS_AVX Vblendps) = @{term "IS_AVX Vblendps"} |  mk_instr_mnemonic (IS_AVX Vblendpd) = @{term "IS_AVX Vblendpd"} |   mk_instr_mnemonic (IS_AVX Vshufpd) = @{term "IS_AVX Vshufpd"} |  mk_instr_mnemonic (IS_AVX Vshufps) = @{term "IS_AVX Vshufps"} |  mk_instr_mnemonic (IS_AVX Vunpcklps) = @{term "IS_AVX Vunpcklps"} 
|  mk_instr_mnemonic (IS_AVX Vblendvps) = @{term "IS_AVX Vblendvps"} |  mk_instr_mnemonic (IS_AVX Vblendvpd) = @{term "IS_AVX Vblendvpd"} |  mk_instr_mnemonic (IS_AVX Vptest) = @{term "IS_AVX Vptest"} |  mk_instr_mnemonic (IS_AVX Vxorps) = @{term "IS_AVX Vxorps"} |  mk_instr_mnemonic (IS_AVX Vxorpd) = @{term "IS_AVX Vxorpd"} 
|  mk_instr_mnemonic (IS_AVX Vorps) = @{term "IS_AVX Vorps"} |  mk_instr_mnemonic (IS_AVX Vorpd) = @{term "IS_AVX Vorpd"} |  mk_instr_mnemonic (IS_AVX Vandnpd) = @{term "IS_AVX Vandnpd"} |  mk_instr_mnemonic (IS_AVX Vandnps) = @{term "IS_AVX Vandnps"} |  mk_instr_mnemonic (IS_AVX Vandpd) = @{term "IS_AVX Vandpd"} |  mk_instr_mnemonic (IS_AVX Vandps) = @{term "IS_AVX Vandps"} 
|  mk_instr_mnemonic (IS_AVX Vbroadcastf128) = @{term "IS_AVX Vbroadcastf128"} |  mk_instr_mnemonic (IS_AVX Vbroadcastsd) = @{term "IS_AVX Vbroadcastsd"} |  mk_instr_mnemonic (IS_AVX Vbroadcastss) = @{term "IS_AVX Vbroadcastss"} |  mk_instr_mnemonic (IS_AVX Vextractf128) = @{term "IS_AVX Vextractf128"} 
|  mk_instr_mnemonic (IS_AVX Vinsertf128) = @{term "IS_AVX Vinsertf128"} |  mk_instr_mnemonic (IS_AVX Vmaskmovps) = @{term "IS_AVX Vmaskmovps"} |  mk_instr_mnemonic (IS_AVX Vmaskmovpd) = @{term "IS_AVX Vmaskmovpd"} |  mk_instr_mnemonic (IS_AVX Vpermilpd) = @{term "IS_AVX Vpermilpd"} 
|  mk_instr_mnemonic (IS_AVX Vpermilps) = @{term "IS_AVX Vpermilps"} |  mk_instr_mnemonic (IS_AVX Vperm2f128) = @{term "IS_AVX Vperm2f128"} |   mk_instr_mnemonic (IS_AVX Vtestps) = @{term "IS_AVX Vtestps"} |  mk_instr_mnemonic (IS_AVX Vtestpd) = @{term "IS_AVX Vtestpd"} |  mk_instr_mnemonic (IS_AVX Vzeroall) = @{term "IS_AVX Vzeroall"} 
|  mk_instr_mnemonic (IS_AVX Vzeroupper) = @{term "IS_AVX Vzeroupper"} |  mk_instr_mnemonic (IS_AVX Vcvtsi2ss) = @{term "IS_AVX Vcvtsi2ss"} |  mk_instr_mnemonic (IS_AVX Vcvtsi2sd) = @{term "IS_AVX Vcvtsi2sd"} |  mk_instr_mnemonic (IS_AVX Vcvtsd2si) = @{term "IS_AVX Vcvtsd2si"} 
|  mk_instr_mnemonic (IS_AVX Vcvttss2si) = @{term "IS_AVX Vcvttss2si"} |  mk_instr_mnemonic (IS_AVX Vcvttsd2si) = @{term "IS_AVX Vcvttsd2si"} |  mk_instr_mnemonic (IS_AVX Vcvtss2si) = @{term "IS_AVX Vcvtss2si"} |  mk_instr_mnemonic (IS_AVX Vcomisd) = @{term "IS_AVX Vcomisd"} |  mk_instr_mnemonic (IS_AVX Vrsqrtss) = @{term "IS_AVX Vrsqrtss"} 
|   mk_instr_mnemonic (IS_AVX Vrcpss) = @{term "IS_AVX Vrcpss"} |  mk_instr_mnemonic (IS_AVX Vucomiss) = @{term "IS_AVX Vucomiss"} |  mk_instr_mnemonic (IS_AVX Vucomisd) = @{term "IS_AVX Vucomisd"} |  mk_instr_mnemonic (IS_AVX Vcomiss) = @{term "IS_AVX Vcomiss"} |  mk_instr_mnemonic (IS_AVX Vaddss) = @{term "IS_AVX Vaddss"} 
|  mk_instr_mnemonic (IS_AVX Vaddsd) = @{term "IS_AVX Vaddsd"} |  mk_instr_mnemonic (IS_AVX Vsubss) = @{term "IS_AVX Vsubss"} |  mk_instr_mnemonic (IS_AVX Vsubsd) = @{term "IS_AVX Vsubsd"} |  mk_instr_mnemonic (IS_AVX Vmulss) = @{term "IS_AVX Vmulss"} |  mk_instr_mnemonic (IS_AVX Vmulsd) = @{term "IS_AVX Vmulsd"} |  mk_instr_mnemonic (IS_AVX Vdivss) = @{term "IS_AVX Vdivss"} 
|  mk_instr_mnemonic (IS_AVX Vdivsd) = @{term "IS_AVX Vdivsd"} |  mk_instr_mnemonic (IS_AVX Vsqrtss) = @{term "IS_AVX Vsqrtss"} |  mk_instr_mnemonic (IS_AVX Vsqrtsd) = @{term "IS_AVX Vsqrtsd"} |  mk_instr_mnemonic (IS_AVX Vcvtss2sd) = @{term "IS_AVX Vcvtss2sd"} |   mk_instr_mnemonic (IS_AVX Vcvtsd2ss) = @{term "IS_AVX Vcvtsd2ss"} 
|  mk_instr_mnemonic (IS_AVX Vminss) = @{term "IS_AVX Vminss"} |  mk_instr_mnemonic (IS_AVX Vminsd) = @{term "IS_AVX Vminsd"} |  mk_instr_mnemonic (IS_AVX Vmaxss) = @{term "IS_AVX Vmaxss"} |  mk_instr_mnemonic (IS_AVX Vmaxsd) = @{term "IS_AVX Vmaxsd"} |  mk_instr_mnemonic (IS_AVX Vpand) = @{term "IS_AVX Vpand"} |  mk_instr_mnemonic (IS_AVX Vpandn) = @{term "IS_AVX Vpandn"} 
|  mk_instr_mnemonic (IS_AVX Vpor) = @{term "IS_AVX Vpor"} |  mk_instr_mnemonic (IS_AVX Vpxor) = @{term "IS_AVX Vpxor"} |  mk_instr_mnemonic (IS_AVX Vpcmpgtb) = @{term "IS_AVX Vpcmpgtb"} |  mk_instr_mnemonic (IS_AVX Vpcmpgtw) = @{term "IS_AVX Vpcmpgtw"} |  mk_instr_mnemonic (IS_AVX Vpcmpgtd) = @{term "IS_AVX Vpcmpgtd"} 
|  mk_instr_mnemonic (IS_AVX Vpmaddwd) = @{term "IS_AVX Vpmaddwd"} |  mk_instr_mnemonic (IS_AVX Vpmaddubsw) = @{term "IS_AVX Vpmaddubsw"} |  mk_instr_mnemonic (IS_AVX Vpavgb) = @{term "IS_AVX Vpavgb"} |   mk_instr_mnemonic (IS_AVX Vpavgw) = @{term "IS_AVX Vpavgw"} |  mk_instr_mnemonic (IS_AVX Vpmuludq) = @{term "IS_AVX Vpmuludq"} 
|  mk_instr_mnemonic (IS_AVX Vpcmpeqb) = @{term "IS_AVX Vpcmpeqb"} |  mk_instr_mnemonic (IS_AVX Vpcmpeqw) = @{term "IS_AVX Vpcmpeqw"} |  mk_instr_mnemonic (IS_AVX Vpcmpeqd) = @{term "IS_AVX Vpcmpeqd"} |  mk_instr_mnemonic (IS_AVX Vpmullw) = @{term "IS_AVX Vpmullw"} |  mk_instr_mnemonic (IS_AVX Vpmulhuw) = @{term "IS_AVX Vpmulhuw"} 
|  mk_instr_mnemonic (IS_AVX Vpmulhw) = @{term "IS_AVX Vpmulhw"} |  mk_instr_mnemonic (IS_AVX Vpsubsw) = @{term "IS_AVX Vpsubsw"} | 

 mk_instr_mnemonic (IS_AVX_2 Vpaddsw) = @{term "IS_AVX_2 Vpaddsw"} |  mk_instr_mnemonic (IS_AVX_2 Vpsadbw) = @{term "IS_AVX_2 Vpsadbw"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddusb) = @{term "IS_AVX_2 Vpaddusb"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddusw) = @{term "IS_AVX_2 Vpaddusw"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddsb) = @{term "IS_AVX_2 Vpaddsb"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpsubusb) = @{term "IS_AVX_2 Vpsubusb"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubusw) = @{term "IS_AVX_2 Vpsubusw"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubsb) = @{term "IS_AVX_2 Vpsubsb"} |  mk_instr_mnemonic (IS_AVX_2 Vpminub) = @{term "IS_AVX_2 Vpminub"} |  mk_instr_mnemonic (IS_AVX_2 Vpminsw) = @{term "IS_AVX_2 Vpminsw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmaxub) = @{term "IS_AVX_2 Vpmaxub"} |  mk_instr_mnemonic (IS_AVX_2 Vpmaxsw) = @{term "IS_AVX_2 Vpmaxsw"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddb) = @{term "IS_AVX_2 Vpaddb"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddw) = @{term "IS_AVX_2 Vpaddw"} |  mk_instr_mnemonic (IS_AVX_2 Vpaddd) = @{term "IS_AVX_2 Vpaddd"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpaddq) = @{term "IS_AVX_2 Vpaddq"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubb) = @{term "IS_AVX_2 Vpsubb"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubw) = @{term "IS_AVX_2 Vpsubw"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubd) = @{term "IS_AVX_2 Vpsubd"} |  mk_instr_mnemonic (IS_AVX_2 Vpsubq) = @{term "IS_AVX_2 Vpsubq"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpsllw) = @{term "IS_AVX_2 Vpsllw"} |  mk_instr_mnemonic (IS_AVX_2 Vpslld) = @{term "IS_AVX_2 Vpslld"} |  mk_instr_mnemonic (IS_AVX_2 Vpsllq) = @{term "IS_AVX_2 Vpsllq"} |  mk_instr_mnemonic (IS_AVX_2 Vpsraw) = @{term "IS_AVX_2 Vpsraw"} |  mk_instr_mnemonic (IS_AVX_2 Vpsrlw) = @{term "IS_AVX_2 Vpsrlw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpsrld) = @{term "IS_AVX_2 Vpsrld"} |  mk_instr_mnemonic (IS_AVX_2 Vpsrlq) = @{term "IS_AVX_2 Vpsrlq"} |  mk_instr_mnemonic (IS_AVX_2 Vpsrad) = @{term "IS_AVX_2 Vpsrad"} |  mk_instr_mnemonic (IS_AVX_2 Vphsubw) = @{term "IS_AVX_2 Vphsubw"} |  mk_instr_mnemonic (IS_AVX_2 Vphsubd) = @{term "IS_AVX_2 Vphsubd"} 
|  mk_instr_mnemonic (IS_AVX_2 Vphsubsw) = @{term "IS_AVX_2 Vphsubsw"} |   mk_instr_mnemonic (IS_AVX_2 Vphaddw) = @{term "IS_AVX_2 Vphaddw"} |  mk_instr_mnemonic (IS_AVX_2 Vphaddd) = @{term "IS_AVX_2 Vphaddd"} |  mk_instr_mnemonic (IS_AVX_2 Vphaddsw) = @{term "IS_AVX_2 Vphaddsw"} |  mk_instr_mnemonic (IS_AVX_2 Vpmulhrsw) = @{term "IS_AVX_2 Vpmulhrsw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpsignb) = @{term "IS_AVX_2 Vpsignb"} |  mk_instr_mnemonic (IS_AVX_2 Vpsignw) = @{term "IS_AVX_2 Vpsignw"} |  mk_instr_mnemonic (IS_AVX_2 Vpsignd) = @{term "IS_AVX_2 Vpsignd"} |  mk_instr_mnemonic (IS_AVX_2 Vpabsb) = @{term "IS_AVX_2 Vpabsb"} |  mk_instr_mnemonic (IS_AVX_2 Vpabsw) = @{term "IS_AVX_2 Vpabsw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpabsd) = @{term "IS_AVX_2 Vpabsd"} |  mk_instr_mnemonic (IS_AVX_2 Vdppd) = @{term "IS_AVX_2 Vdppd"} |  mk_instr_mnemonic (IS_AVX_2 Vphminposuw) = @{term "IS_AVX_2 Vphminposuw"} |  mk_instr_mnemonic (IS_AVX_2 Vmpsadbw) = @{term "IS_AVX_2 Vmpsadbw"} |  mk_instr_mnemonic (IS_AVX_2 Vpmaxsb) = @{term "IS_AVX_2 Vpmaxsb"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmaxsd) = @{term "IS_AVX_2 Vpmaxsd"} |   mk_instr_mnemonic (IS_AVX_2 Vpmaxud) = @{term "IS_AVX_2 Vpmaxud"} |  mk_instr_mnemonic (IS_AVX_2 Vpminsb) = @{term "IS_AVX_2 Vpminsb"} |  mk_instr_mnemonic (IS_AVX_2 Vpminsd) = @{term "IS_AVX_2 Vpminsd"} |  mk_instr_mnemonic (IS_AVX_2 Vpminud) = @{term "IS_AVX_2 Vpminud"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmaxuw) = @{term "IS_AVX_2 Vpmaxuw"} |  mk_instr_mnemonic (IS_AVX_2 Vpminuw) = @{term "IS_AVX_2 Vpminuw"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovsxbw) = @{term "IS_AVX_2 Vpmovsxbw"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovzxbw) = @{term "IS_AVX_2 Vpmovzxbw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmovsxbd) = @{term "IS_AVX_2 Vpmovsxbd"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovzxbd) = @{term "IS_AVX_2 Vpmovzxbd"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovsxbq) = @{term "IS_AVX_2 Vpmovsxbq"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovzxbq) = @{term "IS_AVX_2 Vpmovzxbq"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmovsxwd) = @{term "IS_AVX_2 Vpmovsxwd"} |   mk_instr_mnemonic (IS_AVX_2 Vpmovzxwd) = @{term "IS_AVX_2 Vpmovzxwd"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovsxwq) = @{term "IS_AVX_2 Vpmovsxwq"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovzxwq) = @{term "IS_AVX_2 Vpmovzxwq"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpmovsxdq) = @{term "IS_AVX_2 Vpmovsxdq"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovzxdq) = @{term "IS_AVX_2 Vpmovzxdq"} |  mk_instr_mnemonic (IS_AVX_2 Vpmuldq) = @{term "IS_AVX_2 Vpmuldq"} |  mk_instr_mnemonic (IS_AVX_2 Vpmulld) = @{term "IS_AVX_2 Vpmulld"} |  mk_instr_mnemonic (IS_AVX_2 Vroundsd) = @{term "IS_AVX_2 Vroundsd"} 
|  mk_instr_mnemonic (IS_AVX_2 Vroundss) = @{term "IS_AVX_2 Vroundss"} |  mk_instr_mnemonic (IS_AVX_2 Vpopcnt) = @{term "IS_AVX_2 Vpopcnt"} |  mk_instr_mnemonic (IS_AVX_2 Vpcmpgtq) = @{term "IS_AVX_2 Vpcmpgtq"} |  mk_instr_mnemonic (IS_AVX_2 Vpcmpestri) = @{term "IS_AVX_2 Vpcmpestri"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpcmpestrm) = @{term "IS_AVX_2 Vpcmpestrm"} |   mk_instr_mnemonic (IS_AVX_2 Vpcmpistri) = @{term "IS_AVX_2 Vpcmpistri"} |  mk_instr_mnemonic (IS_AVX_2 Vpcmpistrm) = @{term "IS_AVX_2 Vpcmpistrm"} |  mk_instr_mnemonic (IS_AVX_2 Vpclmulqdq) = @{term "IS_AVX_2 Vpclmulqdq"} 
|  mk_instr_mnemonic (IS_AVX_2 Vaesdec) = @{term "IS_AVX_2 Vaesdec"} |  mk_instr_mnemonic (IS_AVX_2 Vaesdeclast) = @{term "IS_AVX_2 Vaesdeclast"} |  mk_instr_mnemonic (IS_AVX_2 Vaesenc) = @{term "IS_AVX_2 Vaesenc"} |  mk_instr_mnemonic (IS_AVX_2 Vaesenclast) = @{term "IS_AVX_2 Vaesenclast"} 
|  mk_instr_mnemonic (IS_AVX_2 Vaesimx) = @{term "IS_AVX_2 Vaesimx"} |  mk_instr_mnemonic (IS_AVX_2 Vaeskeygenassist) = @{term "IS_AVX_2 Vaeskeygenassist"} |  mk_instr_mnemonic (IS_AVX_2 Vstmxcsr) = @{term "IS_AVX_2 Vstmxcsr"} |  mk_instr_mnemonic (IS_AVX_2 Vmovss) = @{term "IS_AVX_2 Vmovss"} |  mk_instr_mnemonic (IS_AVX_2 Vmovsd) = @{term "IS_AVX_2 Vmovsd"} 
|   mk_instr_mnemonic (IS_AVX_2 Vcmpss) = @{term "IS_AVX_2 Vcmpss"} |  mk_instr_mnemonic (IS_AVX_2 Vcmpsd) = @{term "IS_AVX_2 Vcmpsd"} |  mk_instr_mnemonic (IS_AVX_2 Vmovhps) = @{term "IS_AVX_2 Vmovhps"} |  mk_instr_mnemonic (IS_AVX_2 Vmovhpd) = @{term "IS_AVX_2 Vmovhpd"} |  mk_instr_mnemonic (IS_AVX_2 Vmovlps) = @{term "IS_AVX_2 Vmovlps"} 
|  mk_instr_mnemonic (IS_AVX_2 Vmovlpd) = @{term "IS_AVX_2 Vmovlpd"} |  mk_instr_mnemonic (IS_AVX_2 Vmovlhps) = @{term "IS_AVX_2 Vmovlhps"} |  mk_instr_mnemonic (IS_AVX_2 Vmovhlps) = @{term "IS_AVX_2 Vmovhlps"} |  mk_instr_mnemonic (IS_AVX_2 Vmovq) = @{term "IS_AVX_2 Vmovq"} |  mk_instr_mnemonic (IS_AVX_2 Vmovd) = @{term "IS_AVX_2 Vmovd"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpackuswb) = @{term "IS_AVX_2 Vpackuswb"} |  mk_instr_mnemonic (IS_AVX_2 Vpackssdw) = @{term "IS_AVX_2 Vpackssdw"} |  mk_instr_mnemonic (IS_AVX_2 Vpacksswb) = @{term "IS_AVX_2 Vpacksswb"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpckhbw) = @{term "IS_AVX_2 Vpunpckhbw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpunpckhwd) = @{term "IS_AVX_2 Vpunpckhwd"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpcklbw) = @{term "IS_AVX_2 Vpunpcklbw"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpcklwd) = @{term "IS_AVX_2 Vpunpcklwd"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpckhdq) = @{term "IS_AVX_2 Vpunpckhdq"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpunpckldq) = @{term "IS_AVX_2 Vpunpckldq"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpcklqdq) = @{term "IS_AVX_2 Vpunpcklqdq"} |  mk_instr_mnemonic (IS_AVX_2 Vpunpckhqdq) = @{term "IS_AVX_2 Vpunpckhqdq"} |  mk_instr_mnemonic (IS_AVX_2 Vpshufhw) = @{term "IS_AVX_2 Vpshufhw"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpshuflw) = @{term "IS_AVX_2 Vpshuflw"} |  mk_instr_mnemonic (IS_AVX_2 Vpshufd) = @{term "IS_AVX_2 Vpshufd"} |  mk_instr_mnemonic (IS_AVX_2 Vpmovmskb) = @{term "IS_AVX_2 Vpmovmskb"} |   mk_instr_mnemonic (IS_AVX_2 Vmaskmovdqu) = @{term "IS_AVX_2 Vmaskmovdqu"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpinsrw) = @{term "IS_AVX_2 Vpinsrw"} |  mk_instr_mnemonic (IS_AVX_2 Vpextrw) = @{term "IS_AVX_2 Vpextrw"} |  mk_instr_mnemonic (IS_AVX_2 Vpalignr) = @{term "IS_AVX_2 Vpalignr"} |  mk_instr_mnemonic (IS_AVX_2 Vpshufb) = @{term "IS_AVX_2 Vpshufb"} |  mk_instr_mnemonic (IS_AVX_2 Vextractps) = @{term "IS_AVX_2 Vextractps"} 
|  mk_instr_mnemonic (IS_AVX_2 Vinsertps) = @{term "IS_AVX_2 Vinsertps"} |  mk_instr_mnemonic (IS_AVX_2 Vpackusdw) = @{term "IS_AVX_2 Vpackusdw"} |  mk_instr_mnemonic (IS_AVX_2 Vpcmpeqq) = @{term "IS_AVX_2 Vpcmpeqq"} |  mk_instr_mnemonic (IS_AVX_2 Vpblendvb) = @{term "IS_AVX_2 Vpblendvb"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpblendw) = @{term "IS_AVX_2 Vpblendw"} |  mk_instr_mnemonic (IS_AVX_2 Vpextrb) = @{term "IS_AVX_2 Vpextrb"} |   mk_instr_mnemonic (IS_AVX_2 Vpextrd) = @{term "IS_AVX_2 Vpextrd"} |  mk_instr_mnemonic (IS_AVX_2 Vpextrq) = @{term "IS_AVX_2 Vpextrq"} |  mk_instr_mnemonic (IS_AVX_2 Vpinsrb) = @{term "IS_AVX_2 Vpinsrb"} 
|  mk_instr_mnemonic (IS_AVX_2 Vpinsrd) = @{term "IS_AVX_2 Vpinsrd"} |  mk_instr_mnemonic (IS_AVX_2 Vpinsrq) = @{term "IS_AVX_2 Vpinsrq"} |

  mk_instr_mnemonic (IS_FMA Vfmadd132pd) = @{term "IS_FMA Vfmadd132pd"} |  mk_instr_mnemonic (IS_FMA Vfmadd213pd) = @{term "IS_FMA Vfmadd213pd"} |  mk_instr_mnemonic (IS_FMA Vfmadd231pd) = @{term "IS_FMA Vfmadd231pd"} |  mk_instr_mnemonic (IS_FMA Vfmadd132ps) = @{term "IS_FMA Vfmadd132ps"} 
|  mk_instr_mnemonic (IS_FMA Vfmadd213ps) = @{term "IS_FMA Vfmadd213ps"} |  mk_instr_mnemonic (IS_FMA Vfmadd231ps) = @{term "IS_FMA Vfmadd231ps"} |  mk_instr_mnemonic (IS_FMA Vfmadd132sd) = @{term "IS_FMA Vfmadd132sd"} |  mk_instr_mnemonic (IS_FMA Vfmadd213sd) = @{term "IS_FMA Vfmadd213sd"} 
|  mk_instr_mnemonic (IS_FMA Vfmadd231sd) = @{term "IS_FMA Vfmadd231sd"} |  mk_instr_mnemonic (IS_FMA Vfmadd132ss) = @{term "IS_FMA Vfmadd132ss"} |  mk_instr_mnemonic (IS_FMA Vfmadd213ss) = @{term "IS_FMA Vfmadd213ss"} |   mk_instr_mnemonic (IS_FMA Vfmadd231ss) = @{term "IS_FMA Vfmadd231ss"} 
|  mk_instr_mnemonic (IS_FMA Vfmaddsub132pd) = @{term "IS_FMA Vfmaddsub132pd"} |  mk_instr_mnemonic (IS_FMA Vfmaddsub213pd) = @{term "IS_FMA Vfmaddsub213pd"} |  mk_instr_mnemonic (IS_FMA Vfmaddsub231pd) = @{term "IS_FMA Vfmaddsub231pd"} 
|  mk_instr_mnemonic (IS_FMA Vfmaddsub132ps) = @{term "IS_FMA Vfmaddsub132ps"} |  mk_instr_mnemonic (IS_FMA Vfmaddsub213ps) = @{term "IS_FMA Vfmaddsub213ps"} |  mk_instr_mnemonic (IS_FMA Vfmaddsub231ps) = @{term "IS_FMA Vfmaddsub231ps"} 
|  mk_instr_mnemonic (IS_FMA Vfmsubadd132pd) = @{term "IS_FMA Vfmsubadd132pd"} |  mk_instr_mnemonic (IS_FMA Vfmsubadd213pd) = @{term "IS_FMA Vfmsubadd213pd"} |   mk_instr_mnemonic (IS_FMA Vfmsubadd231pd) = @{term "IS_FMA Vfmsubadd231pd"} 
|  mk_instr_mnemonic (IS_FMA Vfmsubadd132ps) = @{term "IS_FMA Vfmsubadd132ps"} |  mk_instr_mnemonic (IS_FMA Vfmsubadd213ps) = @{term "IS_FMA Vfmsubadd213ps"} |  mk_instr_mnemonic (IS_FMA Vfmsubadd231ps) = @{term "IS_FMA Vfmsubadd231ps"} 
|  mk_instr_mnemonic (IS_FMA Vfmsub132pd) = @{term "IS_FMA Vfmsub132pd"} |  mk_instr_mnemonic (IS_FMA Vfmsub213pd) = @{term "IS_FMA Vfmsub213pd"} |  mk_instr_mnemonic (IS_FMA Vfmsub231pd) = @{term "IS_FMA Vfmsub231pd"} |  mk_instr_mnemonic (IS_FMA Vfmsub132ps) = @{term "IS_FMA Vfmsub132ps"} 
|  mk_instr_mnemonic (IS_FMA Vfmsub213ps) = @{term "IS_FMA Vfmsub213ps"} |  mk_instr_mnemonic (IS_FMA Vfmsub231ps) = @{term "IS_FMA Vfmsub231ps"} |   mk_instr_mnemonic (IS_FMA Vfmsub132sd) = @{term "IS_FMA Vfmsub132sd"} |  mk_instr_mnemonic (IS_FMA Vfmsub213sd) = @{term "IS_FMA Vfmsub213sd"} 
|  mk_instr_mnemonic (IS_FMA Vfmsub231sd) = @{term "IS_FMA Vfmsub231sd"} |  mk_instr_mnemonic (IS_FMA Vfmsub132ss) = @{term "IS_FMA Vfmsub132ss"} |  mk_instr_mnemonic (IS_FMA Vfmsub213ss) = @{term "IS_FMA Vfmsub213ss"} |  mk_instr_mnemonic (IS_FMA Vfmsub231ss) = @{term "IS_FMA Vfmsub231ss"} 
|  mk_instr_mnemonic (IS_FMA Vfnmadd132pd) = @{term "IS_FMA Vfnmadd132pd"} |  mk_instr_mnemonic (IS_FMA Vfnmadd213pd) = @{term "IS_FMA Vfnmadd213pd"} |  mk_instr_mnemonic (IS_FMA Vfnmadd231pd) = @{term "IS_FMA Vfnmadd231pd"} |  mk_instr_mnemonic (IS_FMA Vfnmadd132ps) = @{term "IS_FMA Vfnmadd132ps"} 
|   mk_instr_mnemonic (IS_FMA Vfnmadd213ps) = @{term "IS_FMA Vfnmadd213ps"} |  mk_instr_mnemonic (IS_FMA Vfnmadd231ps) = @{term "IS_FMA Vfnmadd231ps"} |  mk_instr_mnemonic (IS_FMA Vfnmadd132sd) = @{term "IS_FMA Vfnmadd132sd"} |  mk_instr_mnemonic (IS_FMA Vfnmadd213sd) = @{term "IS_FMA Vfnmadd213sd"} 
|  mk_instr_mnemonic (IS_FMA Vfnmadd231sd) = @{term "IS_FMA Vfnmadd231sd"} |  mk_instr_mnemonic (IS_FMA Vfnmadd132ss) = @{term "IS_FMA Vfnmadd132ss"} |  mk_instr_mnemonic (IS_FMA Vfnmadd213ss) = @{term "IS_FMA Vfnmadd213ss"} |  mk_instr_mnemonic (IS_FMA Vfnmadd231ss) = @{term "IS_FMA Vfnmadd231ss"} 
|  mk_instr_mnemonic (IS_FMA Vfnmsub132pd) = @{term "IS_FMA Vfnmsub132pd"} |  mk_instr_mnemonic (IS_FMA Vfnmsub213pd) = @{term "IS_FMA Vfnmsub213pd"} |   mk_instr_mnemonic (IS_FMA Vfnmsub231pd) = @{term "IS_FMA Vfnmsub231pd"} |  mk_instr_mnemonic (IS_FMA Vfnmsub132ps) = @{term "IS_FMA Vfnmsub132ps"} 
|  mk_instr_mnemonic (IS_FMA Vfnmsub213ps) = @{term "IS_FMA Vfnmsub213ps"} |  mk_instr_mnemonic (IS_FMA Vfnmsub231ps) = @{term "IS_FMA Vfnmsub231ps"} |  mk_instr_mnemonic (IS_FMA Vfnmsub132sd) = @{term "IS_FMA Vfnmsub132sd"} |  mk_instr_mnemonic (IS_FMA Vfnmsub213sd) = @{term "IS_FMA Vfnmsub213sd"} 
|  mk_instr_mnemonic (IS_FMA Vfnmsub231sd) = @{term "IS_FMA Vfnmsub231sd"} |  mk_instr_mnemonic (IS_FMA Vfnmsub132ss) = @{term "IS_FMA Vfnmsub132ss"} |  mk_instr_mnemonic (IS_FMA Vfnmsub213ss) = @{term "IS_FMA Vfnmsub213ss"} |  mk_instr_mnemonic (IS_FMA Vfnmsub231ss) = @{term "IS_FMA Vfnmsub231ss"} |

  mk_instr_mnemonic (IS_BM1_BM2 Andn) = @{term "IS_BM1_BM2 Andn"} |  mk_instr_mnemonic (IS_BM1_BM2 Bextr) = @{term "IS_BM1_BM2 Bextr"} |  mk_instr_mnemonic (IS_BM1_BM2 Blsi) = @{term "IS_BM1_BM2 Blsi"} |  mk_instr_mnemonic (IS_BM1_BM2 Blsmsk) = @{term "IS_BM1_BM2 Blsmsk"} |  mk_instr_mnemonic (IS_BM1_BM2 Blsr) = @{term "IS_BM1_BM2 Blsr"} 
|  mk_instr_mnemonic (IS_BM1_BM2 Bzhi) = @{term "IS_BM1_BM2 Bzhi"} |  mk_instr_mnemonic (IS_BM1_BM2 Lzcnt) = @{term "IS_BM1_BM2 Lzcnt"} |  mk_instr_mnemonic (IS_BM1_BM2 Mulx) = @{term "IS_BM1_BM2 Mulx"} |  mk_instr_mnemonic (IS_BM1_BM2 Pdep) = @{term "IS_BM1_BM2 Pdep"} |  mk_instr_mnemonic (IS_BM1_BM2 Pext) = @{term "IS_BM1_BM2 Pext"} |  mk_instr_mnemonic (IS_BM1_BM2 Rorx) = @{term "IS_BM1_BM2 Rorx"} 
|  mk_instr_mnemonic (IS_BM1_BM2 Sarx) = @{term "IS_BM1_BM2 Sarx"} |  mk_instr_mnemonic (IS_BM1_BM2 Shlx) = @{term "IS_BM1_BM2 Shlx"} |  mk_instr_mnemonic (IS_BM1_BM2 Shrx) = @{term "IS_BM1_BM2 Shrx"} |  mk_instr_mnemonic (IS_BM1_BM2 Tzcnt) = @{term "IS_BM1_BM2 Tzcnt"} |
 
  mk_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastb) = @{term "IS_AVX_512_VL_DQ_BW Vpbroadcastb"} |  mk_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastd) = @{term "IS_AVX_512_VL_DQ_BW Vpbroadcastd"} |  mk_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastq) = @{term "IS_AVX_512_VL_DQ_BW Vpbroadcastq"} 
|  mk_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastw) = @{term "IS_AVX_512_VL_DQ_BW Vpbroadcastw"} 

fun 

  toString_instr_mnemonic (IS_8088 Aaa) = "IS_8088 Aaa" |  toString_instr_mnemonic (IS_8088 Aad) = "IS_8088 Aad" |  toString_instr_mnemonic (IS_8088 Aam) = "IS_8088 Aam" |  toString_instr_mnemonic (IS_8088 Aas) = "IS_8088 Aas" |  toString_instr_mnemonic (IS_8088 Adc) = "IS_8088 Adc" |  toString_instr_mnemonic (IS_8088 Add) = "IS_8088 Add" |  toString_instr_mnemonic (IS_8088 And) = "IS_8088 And" 
|  toString_instr_mnemonic (IS_8088 Call) = "IS_8088 Call" |  toString_instr_mnemonic (IS_8088 Cbw) = "IS_8088 Cbw" |  toString_instr_mnemonic (IS_8088 Clc) = "IS_8088 Clc" |  toString_instr_mnemonic (IS_8088 Cld) = "IS_8088 Cld" |  toString_instr_mnemonic (IS_8088 Cli) = "IS_8088 Cli" |  toString_instr_mnemonic (IS_8088 Cmc) = "IS_8088 Cmc" |  toString_instr_mnemonic (IS_8088 Cmp) = "IS_8088 Cmp" 
|  toString_instr_mnemonic (IS_8088 Cmpsb) = "IS_8088 Cmpsb" |  toString_instr_mnemonic (IS_8088 Cwd) = "IS_8088 Cwd" |  toString_instr_mnemonic (IS_8088 Daa) = "IS_8088 Daa" |  toString_instr_mnemonic (IS_8088 Das) = "IS_8088 Das" |  toString_instr_mnemonic (IS_8088 Dec) = "IS_8088 Dec" |  toString_instr_mnemonic (IS_8088 Div) = "IS_8088 Div" |  toString_instr_mnemonic (IS_8088 Esc) = "IS_8088 Esc" 
|  toString_instr_mnemonic (IS_8088 Hlt) = "IS_8088 Hlt" |  toString_instr_mnemonic (IS_8088 Idiv) = "IS_8088 Idiv" |   toString_instr_mnemonic (IS_8088 Imul) = "IS_8088 Imul" |  toString_instr_mnemonic (IS_8088 In) = "IS_8088 In" |  toString_instr_mnemonic (IS_8088 Inc) = "IS_8088 Inc" |  toString_instr_mnemonic (IS_8088 INS_Int) = "IS_8088 Int" |  toString_instr_mnemonic (IS_8088 Into) = "IS_8088 Into" 
|  toString_instr_mnemonic (IS_8088 Iret) = "IS_8088 Iret" |  toString_instr_mnemonic (IS_8088 Ja) = "IS_8088 Ja" |  toString_instr_mnemonic (IS_8088 Jae) = "IS_8088 Jae" |  toString_instr_mnemonic (IS_8088 Jb) = "IS_8088 Jb" |  toString_instr_mnemonic (IS_8088 Jbe) = "IS_8088 Jbe" |  toString_instr_mnemonic (IS_8088 Jc) = "IS_8088 Jc" |  toString_instr_mnemonic (IS_8088 Je) = "IS_8088 Je" |  toString_instr_mnemonic (IS_8088 Jg) = "IS_8088 Jg" 
|  toString_instr_mnemonic (IS_8088 Jge) = "IS_8088 Jge" |  toString_instr_mnemonic (IS_8088 Jl) = "IS_8088 Jl" |  toString_instr_mnemonic (IS_8088 Jle) = "IS_8088 Jle" |  toString_instr_mnemonic (IS_8088 Jna) = "IS_8088 Jna" |  toString_instr_mnemonic (IS_8088 Jnae) = "IS_8088 Jnae" |  toString_instr_mnemonic (IS_8088 Jnb) = "IS_8088 Jnb" |  toString_instr_mnemonic (IS_8088 Jnbe) = "IS_8088 Jnbe" 
|  toString_instr_mnemonic (IS_8088 Jnc) = "IS_8088 Jnc" |  toString_instr_mnemonic (IS_8088 Jne) = "IS_8088 Jne" |  toString_instr_mnemonic (IS_8088 Jng) = "IS_8088 Jng" |  toString_instr_mnemonic (IS_8088 Jnge) = "IS_8088 Jnge" |   toString_instr_mnemonic (IS_8088 Jnl) = "IS_8088 Jnl" |  toString_instr_mnemonic (IS_8088 Jnle) = "IS_8088 Jnle" |  toString_instr_mnemonic (IS_8088 Jno) = "IS_8088 Jno" 
|  toString_instr_mnemonic (IS_8088 Jnp) = "IS_8088 Jnp" |  toString_instr_mnemonic (IS_8088 Jns) = "IS_8088 Jns" |  toString_instr_mnemonic (IS_8088 Jnz) = "IS_8088 Jnz" |  toString_instr_mnemonic (IS_8088 Jo) = "IS_8088 Jo" |  toString_instr_mnemonic (IS_8088 Jp) = "IS_8088 Jp" |  toString_instr_mnemonic (IS_8088 Jpe) = "IS_8088 Jpe" |  toString_instr_mnemonic (IS_8088 Jpo) = "IS_8088 Jpo" |  toString_instr_mnemonic (IS_8088 Js) = "IS_8088 Js" 
|  toString_instr_mnemonic (IS_8088 Jz) = "IS_8088 Jz" |  toString_instr_mnemonic (IS_8088 Jmp) = "IS_8088 Jmp" |  toString_instr_mnemonic (IS_8088 Lahf) = "IS_8088 Lahf" |  toString_instr_mnemonic (IS_8088 Lds) = "IS_8088 Lds" |  toString_instr_mnemonic (IS_8088 Lea) = "IS_8088 Lea" |  toString_instr_mnemonic (IS_8088 Les) = "IS_8088 Les" |  toString_instr_mnemonic (IS_8088 Lock) = "IS_8088 Lock" 
|  toString_instr_mnemonic (IS_8088 Lodsb) = "IS_8088 Lodsb" |  toString_instr_mnemonic (IS_8088 Lodsw) = "IS_8088 Lodsw" |  toString_instr_mnemonic (IS_8088 Loop) = "IS_8088 Loop" |  toString_instr_mnemonic (IS_8088 Loope) = "IS_8088 Loope" |   toString_instr_mnemonic (IS_8088 Loopne) = "IS_8088 Loopne" |  toString_instr_mnemonic (IS_8088 Loopnz) = "IS_8088 Loopnz" 
|  toString_instr_mnemonic (IS_8088 Loopz) = "IS_8088 Loopz" |  toString_instr_mnemonic (IS_8088 Mov) = "IS_8088 Mov" |  toString_instr_mnemonic (IS_8088 Movsb) = "IS_8088 Movsb" |  toString_instr_mnemonic (IS_8088 Movsw) = "IS_8088 Movsw" |  toString_instr_mnemonic (IS_8088 Mul) = "IS_8088 Mul" |  toString_instr_mnemonic (IS_8088 Neg) = "IS_8088 Neg" |  toString_instr_mnemonic (IS_8088 Nop) = "IS_8088 Nop" 
|  toString_instr_mnemonic (IS_8088 Not) = "IS_8088 Not" |  toString_instr_mnemonic (IS_8088 Or) = "IS_8088 Or" |  toString_instr_mnemonic (IS_8088 Out) = "IS_8088 Out" |  toString_instr_mnemonic (IS_8088 Pop) = "IS_8088 Pop" |  toString_instr_mnemonic (IS_8088 Popf) = "IS_8088 Popf" |  toString_instr_mnemonic (IS_8088 Push) = "IS_8088 Push" |  toString_instr_mnemonic (IS_8088 Pushf) = "IS_8088 Pushf" 
|  toString_instr_mnemonic (IS_8088 Rcl) = "IS_8088 Rcl" |  toString_instr_mnemonic (IS_8088 Rcr) = "IS_8088 Rcr" |  toString_instr_mnemonic (IS_8088 Ret) = "IS_8088 Ret" |  toString_instr_mnemonic (IS_8088 Retn) = "IS_8088 Retn" |  toString_instr_mnemonic (IS_8088 Retf) = "IS_8088 Retf" |   toString_instr_mnemonic (IS_8088 Rol) = "IS_8088 Rol" |  toString_instr_mnemonic (IS_8088 Ror) = "IS_8088 Ror" 
|  toString_instr_mnemonic (IS_8088 Sahf) = "IS_8088 Sahf" |  toString_instr_mnemonic (IS_8088 Sal) = "IS_8088 Sal" |  toString_instr_mnemonic (IS_8088 Sar) = "IS_8088 Sar" |  toString_instr_mnemonic (IS_8088 Sbb) = "IS_8088 Sbb" |  toString_instr_mnemonic (IS_8088 Scasb) = "IS_8088 Scasb" |  toString_instr_mnemonic (IS_8088 Scasw) = "IS_8088 Scasw" |  toString_instr_mnemonic (IS_8088 Shl) = "IS_8088 Shl" 
|  toString_instr_mnemonic (IS_8088 Shr) = "IS_8088 Shr" |  toString_instr_mnemonic (IS_8088 Stc) = "IS_8088 Stc" |  toString_instr_mnemonic (IS_8088 Std) = "IS_8088 Std" |  toString_instr_mnemonic (IS_8088 Sti) = "IS_8088 Sti" |  toString_instr_mnemonic (IS_8088 Stosb) = "IS_8088 Stosb" |  toString_instr_mnemonic (IS_8088 Stosw) = "IS_8088 Stosw" |  toString_instr_mnemonic (IS_8088 Sub) = "IS_8088 Sub" 
|  toString_instr_mnemonic (IS_8088 Test) = "IS_8088 Test" |  toString_instr_mnemonic (IS_8088 Wait) = "IS_8088 Wait" |  toString_instr_mnemonic (IS_8088 Xchg) = "IS_8088 Xchg" |  toString_instr_mnemonic (IS_8088 Xlat) = "IS_8088 Xlat" |  toString_instr_mnemonic (IS_8088 Xor) = "IS_8088 Xor" |

  toString_instr_mnemonic (IS_8088_x87 F2xm1) = "IS_8088_x87 F2xm1" |  toString_instr_mnemonic (IS_8088_x87 Fabs) = "IS_8088_x87 Fabs" |  toString_instr_mnemonic (IS_8088_x87 Fadd) = "IS_8088_x87 Fadd" |  toString_instr_mnemonic (IS_8088_x87 Faddp) = "IS_8088_x87 Faddp" |  toString_instr_mnemonic (IS_8088_x87 Fbld) = "IS_8088_x87 Fbld" 
|  toString_instr_mnemonic (IS_8088_x87 Fbstp) = "IS_8088_x87 Fbstp" |  toString_instr_mnemonic (IS_8088_x87 Fchs) = "IS_8088_x87 Fchs" |  toString_instr_mnemonic (IS_8088_x87 Fclex) = "IS_8088_x87 Fclex" |  toString_instr_mnemonic (IS_8088_x87 Fcom) = "IS_8088_x87 Fcom" |  toString_instr_mnemonic (IS_8088_x87 Fcomp) = "IS_8088_x87 Fcomp" 
|  toString_instr_mnemonic (IS_8088_x87 Fcompp) = "IS_8088_x87 Fcompp" |  toString_instr_mnemonic (IS_8088_x87 Decstp) = "IS_8088_x87 Decstp" |  toString_instr_mnemonic (IS_8088_x87 Fdisi) = "IS_8088_x87 Fdisi" |  toString_instr_mnemonic (IS_8088_x87 Fdiv) = "IS_8088_x87 Fdiv" |  toString_instr_mnemonic (IS_8088_x87 Fdivp) = "IS_8088_x87 Fdivp" 
|  toString_instr_mnemonic (IS_8088_x87 Fdivr) = "IS_8088_x87 Fdivr" |  toString_instr_mnemonic (IS_8088_x87 Fdivrp) = "IS_8088_x87 Fdivrp" |  toString_instr_mnemonic (IS_8088_x87 Feni) = "IS_8088_x87 Feni" |   toString_instr_mnemonic (IS_8088_x87 Ffree) = "IS_8088_x87 Ffree" |  toString_instr_mnemonic (IS_8088_x87 Fiadd) = "IS_8088_x87 Fiadd" 
|  toString_instr_mnemonic (IS_8088_x87 Ficom) = "IS_8088_x87 Ficom" |  toString_instr_mnemonic (IS_8088_x87 Ficomp) = "IS_8088_x87 Ficomp" |  toString_instr_mnemonic (IS_8088_x87 Fidiv) = "IS_8088_x87 Fidiv" |  toString_instr_mnemonic (IS_8088_x87 Fidivr) = "IS_8088_x87 Fidivr" |  toString_instr_mnemonic (IS_8088_x87 Fild) = "IS_8088_x87 Fild" 
|  toString_instr_mnemonic (IS_8088_x87 Fimul) = "IS_8088_x87 Fimul" |  toString_instr_mnemonic (IS_8088_x87 Fincstp) = "IS_8088_x87 Fincstp" |  toString_instr_mnemonic (IS_8088_x87 Finit) = "IS_8088_x87 Finit" |  toString_instr_mnemonic (IS_8088_x87 Fist) = "IS_8088_x87 Fist" |  toString_instr_mnemonic (IS_8088_x87 Fistp) = "IS_8088_x87 Fistp" 
|  toString_instr_mnemonic (IS_8088_x87 Fisub) = "IS_8088_x87 Fisub" |  toString_instr_mnemonic (IS_8088_x87 Isubr) = "IS_8088_x87 Isubr" |  toString_instr_mnemonic (IS_8088_x87 Fld) = "IS_8088_x87 Fld" |  toString_instr_mnemonic (IS_8088_x87 Fld1) = "IS_8088_x87 Fld1" |  toString_instr_mnemonic (IS_8088_x87 Fldcw) = "IS_8088_x87 Fldcw" 
|  toString_instr_mnemonic (IS_8088_x87 Fldenv) = "IS_8088_x87 Fldenv" |   toString_instr_mnemonic (IS_8088_x87 Fldenvw) = "IS_8088_x87 Fldenvw" |  toString_instr_mnemonic (IS_8088_x87 Fldl2e) = "IS_8088_x87 Fldl2e" |  toString_instr_mnemonic (IS_8088_x87 Fldl2t) = "IS_8088_x87 Fldl2t" |  toString_instr_mnemonic (IS_8088_x87 Fldlg2) = "IS_8088_x87 Fldlg2" 
|  toString_instr_mnemonic (IS_8088_x87 Fldln2) = "IS_8088_x87 Fldln2" |  toString_instr_mnemonic (IS_8088_x87 Ldpi) = "IS_8088_x87 Ldpi" |  toString_instr_mnemonic (IS_8088_x87 Fldz) = "IS_8088_x87 Fldz" |  toString_instr_mnemonic (IS_8088_x87 Fmul) = "IS_8088_x87 Fmul" |  toString_instr_mnemonic (IS_8088_x87 Fmulp) = "IS_8088_x87 Fmulp" 
|  toString_instr_mnemonic (IS_8088_x87 Fnclex) = "IS_8088_x87 Fnclex" |  toString_instr_mnemonic (IS_8088_x87 Fndisi) = "IS_8088_x87 Fndisi" |  toString_instr_mnemonic (IS_8088_x87 Fneni) = "IS_8088_x87 Fneni" |  toString_instr_mnemonic (IS_8088_x87 Fninit) = "IS_8088_x87 Fninit" |  toString_instr_mnemonic (IS_8088_x87 Fnop) = "IS_8088_x87 Fnop" 
|  toString_instr_mnemonic (IS_8088_x87 Fnsave) = "IS_8088_x87 Fnsave" |  toString_instr_mnemonic (IS_8088_x87 Fnsavew) = "IS_8088_x87 Fnsavew" |  toString_instr_mnemonic (IS_8088_x87 Fnstcw) = "IS_8088_x87 Fnstcw" |   toString_instr_mnemonic (IS_8088_x87 Fnstenv) = "IS_8088_x87 Fnstenv" 
|  toString_instr_mnemonic (IS_8088_x87 Fnstenvw) = "IS_8088_x87 Fnstenvw" |  toString_instr_mnemonic (IS_8088_x87 Fnstsw) = "IS_8088_x87 Fnstsw" |  toString_instr_mnemonic (IS_8088_x87 Fpatan) = "IS_8088_x87 Fpatan" |  toString_instr_mnemonic (IS_8088_x87 Fprem) = "IS_8088_x87 Fprem" |  toString_instr_mnemonic (IS_8088_x87 Fptan) = "IS_8088_x87 Fptan" 
|  toString_instr_mnemonic (IS_8088_x87 Frndint) = "IS_8088_x87 Frndint" |  toString_instr_mnemonic (IS_8088_x87 Frstor) = "IS_8088_x87 Frstor" |  toString_instr_mnemonic (IS_8088_x87 Frstorw) = "IS_8088_x87 Frstorw" |  toString_instr_mnemonic (IS_8088_x87 Save) = "IS_8088_x87 Save" |  toString_instr_mnemonic (IS_8088_x87 Fsavew) = "IS_8088_x87 Fsavew" 
|  toString_instr_mnemonic (IS_8088_x87 Fscale) = "IS_8088_x87 Fscale" |  toString_instr_mnemonic (IS_8088_x87 Fsqrt) = "IS_8088_x87 Fsqrt" |  toString_instr_mnemonic (IS_8088_x87 Fst) = "IS_8088_x87 Fst" |  toString_instr_mnemonic (IS_8088_x87 Fstcw) = "IS_8088_x87 Fstcw" |  toString_instr_mnemonic (IS_8088_x87 Fstenv) = "IS_8088_x87 Fstenv" 
|  toString_instr_mnemonic (IS_8088_x87 Fstenvw) = "IS_8088_x87 Fstenvw" |  toString_instr_mnemonic (IS_8088_x87 Fstp) = "IS_8088_x87 Fstp" |  toString_instr_mnemonic (IS_8088_x87 Fstsw) = "IS_8088_x87 Fstsw" |  toString_instr_mnemonic (IS_8088_x87 Fsub) = "IS_8088_x87 Fsub" |  toString_instr_mnemonic (IS_8088_x87 Fsubp) = "IS_8088_x87 Fsubp" 
|  toString_instr_mnemonic (IS_8088_x87 Fsubr) = "IS_8088_x87 Fsubr" |  toString_instr_mnemonic (IS_8088_x87 Fsubrp) = "IS_8088_x87 Fsubrp" |  toString_instr_mnemonic (IS_8088_x87 Ftst) = "IS_8088_x87 Ftst" |  toString_instr_mnemonic (IS_8088_x87 Fwait) = "IS_8088_x87 Fwait" |  toString_instr_mnemonic (IS_8088_x87 Fxam) = "IS_8088_x87 Fxam" 
|  toString_instr_mnemonic (IS_8088_x87 Fxch) = "IS_8088_x87 Fxch" |  toString_instr_mnemonic (IS_8088_x87 Fxtract) = "IS_8088_x87 Fxtract" |  toString_instr_mnemonic (IS_8088_x87 Fyl2x) = "IS_8088_x87 Fyl2x" |  toString_instr_mnemonic (IS_8088_x87 Fyl2xp1) = "IS_8088_x87 Fyl2xp1" | 

  toString_instr_mnemonic (IS_80188 Bound) = "IS_80188 Bound" |  toString_instr_mnemonic (IS_80188 Enter) = "IS_80188 Enter" |  toString_instr_mnemonic (IS_80188 Ins) = "IS_80188 Ins" |  toString_instr_mnemonic (IS_80188 Leave) = "IS_80188 Leave" |  toString_instr_mnemonic (IS_80188 Outs) = "IS_80188 Outs" |  toString_instr_mnemonic (IS_80188 Popa) = "IS_80188 Popa" 
|  toString_instr_mnemonic (IS_80188 Pusha) = "IS_80188 Pusha" | 

  toString_instr_mnemonic (IS_80286 Arpl) = "IS_80286 Arpl" |  toString_instr_mnemonic (IS_80286 Clts) = "IS_80286 Clts" |  toString_instr_mnemonic (IS_80286 Lar) = "IS_80286 Lar" |  toString_instr_mnemonic (IS_80286 Lgdt) = "IS_80286 Lgdt" |  toString_instr_mnemonic (IS_80286 Lidt) = "IS_80286 Lidt" |  toString_instr_mnemonic (IS_80286 Lldt) = "IS_80286 Lldt" 
|  toString_instr_mnemonic (IS_80286 Lmsw) = "IS_80286 Lmsw" |  toString_instr_mnemonic (IS_80286 Loadall) = "IS_80286 Loadall" |  toString_instr_mnemonic (IS_80286 Lsl) = "IS_80286 Lsl" |  toString_instr_mnemonic (IS_80286 Ltr) = "IS_80286 Ltr" |  toString_instr_mnemonic (IS_80286 Sgdt) = "IS_80286 Sgdt" |  toString_instr_mnemonic (IS_80286 Sidt) = "IS_80286 Sidt" 
|  toString_instr_mnemonic (IS_80286 Sldt) = "IS_80286 Sldt" |  toString_instr_mnemonic (IS_80286 Smsw) = "IS_80286 Smsw" |  toString_instr_mnemonic (IS_80286 Str) = "IS_80286 Str" |  toString_instr_mnemonic (IS_80286 Verr) = "IS_80286 Verr" |  toString_instr_mnemonic (IS_80286 Verw) = "IS_80286 Verw" |

  toString_instr_mnemonic (IS_80286_x87 Fsetpm) = "IS_80286_x87 Fsetpm" |

  toString_instr_mnemonic (IS_80386 Bsf) = "IS_80386 Bsf" |  toString_instr_mnemonic (IS_80386 Bsr) = "IS_80386 Bsr" |  toString_instr_mnemonic (IS_80386 Bt) = "IS_80386 Bt" |  toString_instr_mnemonic (IS_80386 Btc) = "IS_80386 Btc" |  toString_instr_mnemonic (IS_80386 Btr) = "IS_80386 Btr" |  toString_instr_mnemonic (IS_80386 Bts) = "IS_80386 Bts" |  toString_instr_mnemonic (IS_80386 Cdq) = "IS_80386 Cdq" 
|  toString_instr_mnemonic (IS_80386 Cwde) = "IS_80386 Cwde" |  toString_instr_mnemonic (IS_80386 Ibts) = "IS_80386 Ibts" |  toString_instr_mnemonic (IS_80386 Insd) = "IS_80386 Insd" |  toString_instr_mnemonic (IS_80386 Iretd) = "IS_80386 Iretd" |  toString_instr_mnemonic (IS_80386 Iretf) = "IS_80386 Iretf" |  toString_instr_mnemonic (IS_80386 Jecxz) = "IS_80386 Jecxz" 
|  toString_instr_mnemonic (IS_80386 Lfs) = "IS_80386 Lfs" |  toString_instr_mnemonic (IS_80386 Lgs) = "IS_80386 Lgs" |  toString_instr_mnemonic (IS_80386 Lss) = "IS_80386 Lss" |  toString_instr_mnemonic (IS_80386 Lodsd) = "IS_80386 Lodsd" |  toString_instr_mnemonic (IS_80386 Loopw) = "IS_80386 Loopw" |  toString_instr_mnemonic (IS_80386 Loopzw) = "IS_80386 Loopzw" 
|  toString_instr_mnemonic (IS_80386 Loopew) = "IS_80386 Loopew" |   toString_instr_mnemonic (IS_80386 Loopnzw) = "IS_80386 Loopnzw" |  toString_instr_mnemonic (IS_80386 Loopnew) = "IS_80386 Loopnew" |  toString_instr_mnemonic (IS_80386 Loopd) = "IS_80386 Loopd" |  toString_instr_mnemonic (IS_80386 Loopzd) = "IS_80386 Loopzd" 
|  toString_instr_mnemonic (IS_80386 Looped) = "IS_80386 Looped" |  toString_instr_mnemonic (IS_80386 Loopnzd) = "IS_80386 Loopnzd" |  toString_instr_mnemonic (IS_80386 Loopned) = "IS_80386 Loopned" |  toString_instr_mnemonic (IS_80386 Movsx) = "IS_80386 Movsx" |  toString_instr_mnemonic (IS_80386 Movzx) = "IS_80386 Movzx" 
|  toString_instr_mnemonic (IS_80386 Outsd) = "IS_80386 Outsd" |  toString_instr_mnemonic (IS_80386 Popad) = "IS_80386 Popad" |  toString_instr_mnemonic (IS_80386 Popfd) = "IS_80386 Popfd" |  toString_instr_mnemonic (IS_80386 Pushad) = "IS_80386 Pushad" |  toString_instr_mnemonic (IS_80386 Pushfd) = "IS_80386 Pushfd" 
|  toString_instr_mnemonic (IS_80386 Scasd) = "IS_80386 Scasd" |  toString_instr_mnemonic (IS_80386 Seta) = "IS_80386 Seta" |   toString_instr_mnemonic (IS_80386 Setae) = "IS_80386 Setae" |  toString_instr_mnemonic (IS_80386 Setb) = "IS_80386 Setb" |  toString_instr_mnemonic (IS_80386 Setbe) = "IS_80386 Setbe" |  toString_instr_mnemonic (IS_80386 Setc) = "IS_80386 Setc" 
|  toString_instr_mnemonic (IS_80386 Sete) = "IS_80386 Sete" |  toString_instr_mnemonic (IS_80386 Setg) = "IS_80386 Setg" |  toString_instr_mnemonic (IS_80386 Setge) = "IS_80386 Setge" |  toString_instr_mnemonic (IS_80386 Setl) = "IS_80386 Setl" |  toString_instr_mnemonic (IS_80386 Setle) = "IS_80386 Setle" |  toString_instr_mnemonic (IS_80386 Setna) = "IS_80386 Setna" 
|  toString_instr_mnemonic (IS_80386 Setnae) = "IS_80386 Setnae" |  toString_instr_mnemonic (IS_80386 Setnb) = "IS_80386 Setnb" |  toString_instr_mnemonic (IS_80386 Setnbe) = "IS_80386 Setnbe" |  toString_instr_mnemonic (IS_80386 Setnc) = "IS_80386 Setnc" |  toString_instr_mnemonic (IS_80386 Setne) = "IS_80386 Setne" |  toString_instr_mnemonic (IS_80386 Setng) = "IS_80386 Setng" 
|  toString_instr_mnemonic (IS_80386 Setnge) = "IS_80386 Setnge" |  toString_instr_mnemonic (IS_80386 Setnl) = "IS_80386 Setnl" |   toString_instr_mnemonic (IS_80386 Setnle) = "IS_80386 Setnle" |  toString_instr_mnemonic (IS_80386 Setno) = "IS_80386 Setno" |  toString_instr_mnemonic (IS_80386 Setnp) = "IS_80386 Setnp" |  toString_instr_mnemonic (IS_80386 Setns) = "IS_80386 Setns" 
|  toString_instr_mnemonic (IS_80386 Setnz) = "IS_80386 Setnz" |  toString_instr_mnemonic (IS_80386 Seto) = "IS_80386 Seto" |  toString_instr_mnemonic (IS_80386 Setp) = "IS_80386 Setp" |  toString_instr_mnemonic (IS_80386 Setpe) = "IS_80386 Setpe" |  toString_instr_mnemonic (IS_80386 Setpo) = "IS_80386 Setpo" |  toString_instr_mnemonic (IS_80386 Sets) = "IS_80386 Sets" 
|  toString_instr_mnemonic (IS_80386 Setz) = "IS_80386 Setz" |

  toString_instr_mnemonic (IS_80386_x87 Fcos) = "IS_80386_x87 Fcos" |  toString_instr_mnemonic (IS_80386_x87 Fldenvd) = "IS_80386_x87 Fldenvd" |  toString_instr_mnemonic (IS_80386_x87 Fsaved) = "IS_80386_x87 Fsaved" |  toString_instr_mnemonic (IS_80386_x87 Fstenvd) = "IS_80386_x87 Fstenvd" |  toString_instr_mnemonic (IS_80386_x87 Fprem1) = "IS_80386_x87 Fprem1" 
|  toString_instr_mnemonic (IS_80386_x87 Frstord) = "IS_80386_x87 Frstord" |  toString_instr_mnemonic (IS_80386_x87 Fsin) = "IS_80386_x87 Fsin" |  toString_instr_mnemonic (IS_80386_x87 Fsincos) = "IS_80386_x87 Fsincos" |  toString_instr_mnemonic (IS_80386_x87 Fucom) = "IS_80386_x87 Fucom" 
|  toString_instr_mnemonic (IS_80386_x87 Fucomp) = "IS_80386_x87 Fucomp" |  toString_instr_mnemonic (IS_80386_x87 Fucompp) = "IS_80386_x87 Fucompp" |

  toString_instr_mnemonic (IS_80486 Bswap) = "IS_80486 Bswap" |  toString_instr_mnemonic (IS_80486 Cmpxchg) = "IS_80486 Cmpxchg" |  toString_instr_mnemonic (IS_80486 Invd) = "IS_80486 Invd" |  toString_instr_mnemonic (IS_80486 Invlpg) = "IS_80486 Invlpg" |  toString_instr_mnemonic (IS_80486 Wbinvd) = "IS_80486 Wbinvd" |  toString_instr_mnemonic (IS_80486 Xadd) = "IS_80486 Xadd" |

  toString_instr_mnemonic (IS_Pentium Cpuid) = "IS_Pentium Cpuid" |  toString_instr_mnemonic (IS_Pentium Cmpxchg8b) = "IS_Pentium Cmpxchg8b" |  toString_instr_mnemonic (IS_Pentium Rdmsr) = "IS_Pentium Rdmsr" |  toString_instr_mnemonic (IS_Pentium Rdtsc) = "IS_Pentium Rdtsc" |  toString_instr_mnemonic (IS_Pentium Wrmsr) = "IS_Pentium Wrmsr" 
|  toString_instr_mnemonic (IS_Pentium Rsm) = "IS_Pentium Rsm" |

 toString_instr_mnemonic  (IS_PentiumMMX Rdpmc) = "IS_PentiumMMX Rdpmc" |

  toString_instr_mnemonic (IS_PentiumMMX_MMX Emms) = "IS_PentiumMMX_MMX Emms" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Movd) = "IS_PentiumMMX_MMX Movd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Movq) = "IS_PentiumMMX_MMX Movq" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Packssdw) = "IS_PentiumMMX_MMX Packssdw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Packsswb) = "IS_PentiumMMX_MMX Packsswb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Packuswb) = "IS_PentiumMMX_MMX Packuswb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddb) = "IS_PentiumMMX_MMX Paddb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddw) = "IS_PentiumMMX_MMX Paddw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddd) = "IS_PentiumMMX_MMX Paddd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddq) = "IS_PentiumMMX_MMX Paddq" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddsb) = "IS_PentiumMMX_MMX Paddsb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddsw) = "IS_PentiumMMX_MMX Paddsw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddusb) = "IS_PentiumMMX_MMX Paddusb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Paddusw) = "IS_PentiumMMX_MMX Paddusw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pand) = "IS_PentiumMMX_MMX Pand" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pandn) = "IS_PentiumMMX_MMX Pandn" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Por) = "IS_PentiumMMX_MMX Por" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pxor) = "IS_PentiumMMX_MMX Pxor" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqb) = "IS_PentiumMMX_MMX Pcmpeqb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqw) = "IS_PentiumMMX_MMX Pcmpeqw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpeqd) = "IS_PentiumMMX_MMX Pcmpeqd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtb) = "IS_PentiumMMX_MMX Pcmpgtb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtw) = "IS_PentiumMMX_MMX Pcmpgtw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pcmpgtd) = "IS_PentiumMMX_MMX Pcmpgtd" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Pmaddwd) = "IS_PentiumMMX_MMX Pmaddwd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pmulhw) = "IS_PentiumMMX_MMX Pmulhw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Pmullw) = "IS_PentiumMMX_MMX Pmullw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psllw) = "IS_PentiumMMX_MMX Psllw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Pslld) = "IS_PentiumMMX_MMX Pslld" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psllq) = "IS_PentiumMMX_MMX Psllq" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psrad) = "IS_PentiumMMX_MMX Psrad" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psraw) = "IS_PentiumMMX_MMX Psraw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Psrlw) = "IS_PentiumMMX_MMX Psrlw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psrld) = "IS_PentiumMMX_MMX Psrld" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psrlq) = "IS_PentiumMMX_MMX Psrlq" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubb) = "IS_PentiumMMX_MMX Psubb" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubw) = "IS_PentiumMMX_MMX Psubw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubd) = "IS_PentiumMMX_MMX Psubd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubsb) = "IS_PentiumMMX_MMX Psubsb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubsw) = "IS_PentiumMMX_MMX Psubsw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubusb) = "IS_PentiumMMX_MMX Psubusb" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Psubusw) = "IS_PentiumMMX_MMX Psubusw" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Punpckhbw) = "IS_PentiumMMX_MMX Punpckhbw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Punpckhwd) = "IS_PentiumMMX_MMX Punpckhwd" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Punpckhdq) = "IS_PentiumMMX_MMX Punpckhdq" |  toString_instr_mnemonic (IS_PentiumMMX_MMX Punpcklbw) = "IS_PentiumMMX_MMX Punpcklbw" 
|  toString_instr_mnemonic (IS_PentiumMMX_MMX Punpcklwd) = "IS_PentiumMMX_MMX Punpcklwd" |   toString_instr_mnemonic (IS_PentiumMMX_MMX Punpckldq) = "IS_PentiumMMX_MMX Punpckldq" |

  toString_instr_mnemonic (IS_PentiumPro Cmova) = "IS_PentiumPro Cmova" |  toString_instr_mnemonic (IS_PentiumPro Cmovae) = "IS_PentiumPro Cmovae" |  toString_instr_mnemonic (IS_PentiumPro Cmovb) = "IS_PentiumPro Cmovb" |  toString_instr_mnemonic (IS_PentiumPro Cmovbe) = "IS_PentiumPro Cmovbe" |  toString_instr_mnemonic (IS_PentiumPro Cmovc) = "IS_PentiumPro Cmovc" 
|  toString_instr_mnemonic (IS_PentiumPro Cmove) = "IS_PentiumPro Cmove" |  toString_instr_mnemonic (IS_PentiumPro Cmovg) = "IS_PentiumPro Cmovg" |  toString_instr_mnemonic (IS_PentiumPro Cmovge) = "IS_PentiumPro Cmovge" |  toString_instr_mnemonic (IS_PentiumPro Cmovl) = "IS_PentiumPro Cmovl" |  toString_instr_mnemonic (IS_PentiumPro Cmovle) = "IS_PentiumPro Cmovle" 
|  toString_instr_mnemonic (IS_PentiumPro Cmovna) = "IS_PentiumPro Cmovna" |  toString_instr_mnemonic (IS_PentiumPro Cmovnae) = "IS_PentiumPro Cmovnae" |  toString_instr_mnemonic (IS_PentiumPro Cmovnb) = "IS_PentiumPro Cmovnb" |  toString_instr_mnemonic (IS_PentiumPro Cmovnbe) = "IS_PentiumPro Cmovnbe" 
|  toString_instr_mnemonic (IS_PentiumPro Cmovnc) = "IS_PentiumPro Cmovnc" |  toString_instr_mnemonic (IS_PentiumPro Cmovne) = "IS_PentiumPro Cmovne" |   toString_instr_mnemonic (IS_PentiumPro Cmovng) = "IS_PentiumPro Cmovng" |  toString_instr_mnemonic (IS_PentiumPro Cmovnge) = "IS_PentiumPro Cmovnge" 
|  toString_instr_mnemonic (IS_PentiumPro Cmovnl) = "IS_PentiumPro Cmovnl" |  toString_instr_mnemonic (IS_PentiumPro Cmovnle) = "IS_PentiumPro Cmovnle" |  toString_instr_mnemonic (IS_PentiumPro Cmovno) = "IS_PentiumPro Cmovno" |  toString_instr_mnemonic (IS_PentiumPro Cmovnp) = "IS_PentiumPro Cmovnp" 
|  toString_instr_mnemonic (IS_PentiumPro Cmovns) = "IS_PentiumPro Cmovns" |  toString_instr_mnemonic (IS_PentiumPro Cmovnz) = "IS_PentiumPro Cmovnz" |  toString_instr_mnemonic (IS_PentiumPro Cmovo) = "IS_PentiumPro Cmovo" |  toString_instr_mnemonic (IS_PentiumPro Cmovp) = "IS_PentiumPro Cmovp" 
|  toString_instr_mnemonic (IS_PentiumPro Cmovpe) = "IS_PentiumPro Cmovpe" |  toString_instr_mnemonic (IS_PentiumPro Cmovpo) = "IS_PentiumPro Cmovpo" |  toString_instr_mnemonic (IS_PentiumPro Cmovs) = "IS_PentiumPro Cmovs" |  toString_instr_mnemonic (IS_PentiumPro Cmovz) = "IS_PentiumPro Cmovz" |  toString_instr_mnemonic (IS_PentiumPro Ud2) = "IS_PentiumPro Ud2" |

  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovb) = "IS_PentiumPro_x87 Fcmovb" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovbe) = "IS_PentiumPro_x87 Fcmovbe" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmove) = "IS_PentiumPro_x87 Fcmove" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovnb) = "IS_PentiumPro_x87 Fcmovnb" 
|  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovnbe) = "IS_PentiumPro_x87 Fcmovnbe" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovne) = "IS_PentiumPro_x87 Fcmovne" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovnu) = "IS_PentiumPro_x87 Fcmovnu" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcmovu) = "IS_PentiumPro_x87 Fcmovu" 
|  toString_instr_mnemonic (IS_PentiumPro_x87 Fcomi) = "IS_PentiumPro_x87 Fcomi" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fcomip) = "IS_PentiumPro_x87 Fcomip" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fucomi) = "IS_PentiumPro_x87 Fucomi" |  toString_instr_mnemonic (IS_PentiumPro_x87 Fucomip) = "IS_PentiumPro_x87 Fucomip" |

  toString_instr_mnemonic (IS_PentiumII Sysenter) = "IS_PentiumII Sysenter" |  toString_instr_mnemonic (IS_PentiumII Sysexit) = "IS_PentiumII Sysexit" |

  toString_instr_mnemonic (IS_SSE Maskmovq) = "IS_SSE Maskmovq" |  toString_instr_mnemonic (IS_SSE Movntq) = "IS_SSE Movntq" |  toString_instr_mnemonic (IS_SSE Prefetcht0) = "IS_SSE Prefetcht0" |  toString_instr_mnemonic (IS_SSE Prefetcht1) = "IS_SSE Prefetcht1" 
|  toString_instr_mnemonic (IS_SSE Prefetcht2) = "IS_SSE Prefetcht2" |  toString_instr_mnemonic (IS_SSE Prefetchnta) = "IS_SSE Prefetchnta" |  toString_instr_mnemonic (IS_SSE Sfence) = "IS_SSE Sfence" |

  toString_instr_mnemonic (IS_SSE_x87 Fxrstor) = "IS_SSE_x87 Fxrstor" |  toString_instr_mnemonic (IS_SSE_x87 Fxsave) = "IS_SSE_x87 Fxsave" |

  toString_instr_mnemonic (IS_SSE_SIMDMMX Pshufw) = "IS_SSE_SIMDMMX Pshufw" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pinsrw) = "IS_SSE_SIMDMMX Pinsrw" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pextrw) = "IS_SSE_SIMDMMX Pextrw" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pmovmskb) = "IS_SSE_SIMDMMX Pmovmskb" 
|  toString_instr_mnemonic (IS_SSE_SIMDMMX Pminub) = "IS_SSE_SIMDMMX Pminub" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pmaxub) = "IS_SSE_SIMDMMX Pmaxub" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pavgb) = "IS_SSE_SIMDMMX Pavgb" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pavgw) = "IS_SSE_SIMDMMX Pavgw" 
|  toString_instr_mnemonic (IS_SSE_SIMDMMX Pmulhuw) = "IS_SSE_SIMDMMX Pmulhuw" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pminsw) = "IS_SSE_SIMDMMX Pminsw" |  toString_instr_mnemonic (IS_SSE_SIMDMMX Pmaxsw) = "IS_SSE_SIMDMMX Pmaxsw"   
|  toString_instr_mnemonic (IS_SSE_SIMDMMX Psadbw) = "IS_SSE_SIMDMMX Psadbw" |

toString_instr_mnemonic (IS_SSE_SIMD Andps) = "IS_SSE_SIMD Andps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Andnps) = "IS_SSE_SIMD Andnps" |  toString_instr_mnemonic (IS_SSE_SIMD Orps) = "IS_SSE_SIMD Orps" |  toString_instr_mnemonic (IS_SSE_SIMD Xorps) = "IS_SSE_SIMD Xorps" |  toString_instr_mnemonic (IS_SSE_SIMD Movups) = "IS_SSE_SIMD Movups" 
|  toString_instr_mnemonic (IS_SSE_SIMD Movss) = "IS_SSE_SIMD Movss" |  toString_instr_mnemonic (IS_SSE_SIMD Movhlps) = "IS_SSE_SIMD Movhlps" |  toString_instr_mnemonic (IS_SSE_SIMD Movlps) = "IS_SSE_SIMD Movlps" |  toString_instr_mnemonic (IS_SSE_SIMD Unpcklps) = "IS_SSE_SIMD Unpcklps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Unpckhps) = "IS_SSE_SIMD Unpckhps" |  toString_instr_mnemonic (IS_SSE_SIMD Movlhps) = "IS_SSE_SIMD Movlhps" |  toString_instr_mnemonic (IS_SSE_SIMD Movhps) = "IS_SSE_SIMD Movhps" |  toString_instr_mnemonic (IS_SSE_SIMD Movaps) = "IS_SSE_SIMD Movaps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Movmskps) = "IS_SSE_SIMD Movmskps" |  toString_instr_mnemonic (IS_SSE_SIMD Cvtpi2ps) = "IS_SSE_SIMD Cvtpi2ps" |  toString_instr_mnemonic (IS_SSE_SIMD Cvtsi2ss) = "IS_SSE_SIMD Cvtsi2ss" |  toString_instr_mnemonic (IS_SSE_SIMD Movntps) = "IS_SSE_SIMD Movntps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Cvttps2pi) = "IS_SSE_SIMD Cvttps2pi" |  toString_instr_mnemonic (IS_SSE_SIMD Cvttss2si) = "IS_SSE_SIMD Cvttss2si" |   toString_instr_mnemonic (IS_SSE_SIMD Cvtps2pi) = "IS_SSE_SIMD Cvtps2pi" |  toString_instr_mnemonic (IS_SSE_SIMD Cvtss2si) = "IS_SSE_SIMD Cvtss2si" 
|  toString_instr_mnemonic (IS_SSE_SIMD Ucomiss) = "IS_SSE_SIMD Ucomiss" |  toString_instr_mnemonic (IS_SSE_SIMD Comiss) = "IS_SSE_SIMD Comiss" |  toString_instr_mnemonic (IS_SSE_SIMD Sqrtps) = "IS_SSE_SIMD Sqrtps" |  toString_instr_mnemonic (IS_SSE_SIMD Sqrtss) = "IS_SSE_SIMD Sqrtss" 
|  toString_instr_mnemonic (IS_SSE_SIMD Rsqrtps) = "IS_SSE_SIMD Rsqrtps" |  toString_instr_mnemonic (IS_SSE_SIMD Rsqrtss) = "IS_SSE_SIMD Rsqrtss" |  toString_instr_mnemonic (IS_SSE_SIMD Rcpps) = "IS_SSE_SIMD Rcpps" |  toString_instr_mnemonic (IS_SSE_SIMD Rcpss) = "IS_SSE_SIMD Rcpss" 
|  toString_instr_mnemonic (IS_SSE_SIMD Addps) = "IS_SSE_SIMD Addps" |  toString_instr_mnemonic (IS_SSE_SIMD Addss) = "IS_SSE_SIMD Addss" |  toString_instr_mnemonic (IS_SSE_SIMD Mulps) = "IS_SSE_SIMD Mulps" |  toString_instr_mnemonic (IS_SSE_SIMD Mulss) = "IS_SSE_SIMD Mulss" |  toString_instr_mnemonic (IS_SSE_SIMD Subps) = "IS_SSE_SIMD Subps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Subss) = "IS_SSE_SIMD Subss" |   toString_instr_mnemonic (IS_SSE_SIMD Minps) = "IS_SSE_SIMD Minps" |  toString_instr_mnemonic (IS_SSE_SIMD Minss) = "IS_SSE_SIMD Minss" |  toString_instr_mnemonic (IS_SSE_SIMD Divps) = "IS_SSE_SIMD Divps" 
|  toString_instr_mnemonic (IS_SSE_SIMD Divss) = "IS_SSE_SIMD Divss" |  toString_instr_mnemonic (IS_SSE_SIMD Maxps) = "IS_SSE_SIMD Maxps" |  toString_instr_mnemonic (IS_SSE_SIMD Maxss) = "IS_SSE_SIMD Maxss" |  toString_instr_mnemonic (IS_SSE_SIMD Ldmxcsr) = "IS_SSE_SIMD Ldmxcsr" 
|  toString_instr_mnemonic (IS_SSE_SIMD Stmxcsr) = "IS_SSE_SIMD Stmxcsr" |  toString_instr_mnemonic (IS_SSE_SIMD Cmpps) = "IS_SSE_SIMD Cmpps" |  toString_instr_mnemonic (IS_SSE_SIMD Cmpss) = "IS_SSE_SIMD Cmpss" |  toString_instr_mnemonic (IS_SSE_SIMD Shufps) = "IS_SSE_SIMD Shufps" |

  toString_instr_mnemonic (IS_SSE2 Clflush) = "IS_SSE2 Clflush" |  toString_instr_mnemonic (IS_SSE2 Lfence) = "IS_SSE2 Lfence" |  toString_instr_mnemonic (IS_SSE2 Mfence) = "IS_SSE2 Mfence" |  toString_instr_mnemonic (IS_SSE2 Movnti) = "IS_SSE2 Movnti" |  toString_instr_mnemonic (IS_SSE2 Pause) = "IS_SSE2 Pause" |

  toString_instr_mnemonic (IS_SSE2_SIMDMMX Psubq) = "IS_SSE2_SIMDMMX Psubq" |  toString_instr_mnemonic (IS_SSE2_SIMDMMX Pmuludq) = "IS_SSE2_SIMDMMX Pmuludq" |

  toString_instr_mnemonic (IS_SSE2_SIMD Movapd) = "IS_SSE2_SIMD Movapd" |  toString_instr_mnemonic (IS_SSE2_SIMD Movntpd) = "IS_SSE2_SIMD Movntpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Movhpd) = "IS_SSE2_SIMD Movhpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Movlpd) = "IS_SSE2_SIMD Movlpd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Movupd) = "IS_SSE2_SIMD Movupd" |  toString_instr_mnemonic (IS_SSE2_SIMD Movmskpd) = "IS_SSE2_SIMD Movmskpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Movsd) = "IS_SSE2_SIMD Movsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Addpd) = "IS_SSE2_SIMD Addpd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Addsd) = "IS_SSE2_SIMD Addsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Divpd) = "IS_SSE2_SIMD Divpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Divsd) = "IS_SSE2_SIMD Divsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Maxpd) = "IS_SSE2_SIMD Maxpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Maxsd) = "IS_SSE2_SIMD Maxsd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Minpd) = "IS_SSE2_SIMD Minpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Minsd) = "IS_SSE2_SIMD Minsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Mulpd) = "IS_SSE2_SIMD Mulpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Mulsd) = "IS_SSE2_SIMD Mulsd" |   toString_instr_mnemonic (IS_SSE2_SIMD Sqrtpd) = "IS_SSE2_SIMD Sqrtpd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Sqrtsd) = "IS_SSE2_SIMD Sqrtsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Subpd) = "IS_SSE2_SIMD Subpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Subsd) = "IS_SSE2_SIMD Subsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Andpd) = "IS_SSE2_SIMD Andpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Andnpd) = "IS_SSE2_SIMD Andnpd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Orpd) = "IS_SSE2_SIMD Orpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Xorpd) = "IS_SSE2_SIMD Xorpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Cmppd) = "IS_SSE2_SIMD Cmppd" |  toString_instr_mnemonic (IS_SSE2_SIMD Cmpsd) = "IS_SSE2_SIMD Cmpsd" |  toString_instr_mnemonic (IS_SSE2_SIMD Comisd) = "IS_SSE2_SIMD Comisd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Ucomisd) = "IS_SSE2_SIMD Ucomisd" |  toString_instr_mnemonic (IS_SSE2_SIMD Shufpd) = "IS_SSE2_SIMD Shufpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Unpckhpd) = "IS_SSE2_SIMD Unpckhpd" |  toString_instr_mnemonic (IS_SSE2_SIMD Unpcklpd) = "IS_SSE2_SIMD Unpcklpd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Cvtdq2pd) = "IS_SSE2_SIMD Cvtdq2pd" |   toString_instr_mnemonic (IS_SSE2_SIMD Cvtdq2ps) = "IS_SSE2_SIMD Cvtdq2ps" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtpd2dq) = "IS_SSE2_SIMD Cvtpd2dq" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtpd2pi) = "IS_SSE2_SIMD Cvtpd2pi" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Cvtpd2ps) = "IS_SSE2_SIMD Cvtpd2ps" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtpi2pd) = "IS_SSE2_SIMD Cvtpi2pd" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtps2dq) = "IS_SSE2_SIMD Cvtps2dq" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtps2pd) = "IS_SSE2_SIMD Cvtps2pd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Cvtsd2si) = "IS_SSE2_SIMD Cvtsd2si" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtsd2ss) = "IS_SSE2_SIMD Cvtsd2ss" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtsi2sd) = "IS_SSE2_SIMD Cvtsi2sd" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvtss2sd) = "IS_SSE2_SIMD Cvtss2sd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Cvttpd2dq) = "IS_SSE2_SIMD Cvttpd2dq" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvttpd2pi) = "IS_SSE2_SIMD Cvttpd2pi" |   toString_instr_mnemonic (IS_SSE2_SIMD Cvttps2dq) = "IS_SSE2_SIMD Cvttps2dq" |  toString_instr_mnemonic (IS_SSE2_SIMD Cvttsd2si) = "IS_SSE2_SIMD Cvttsd2si"   
|  toString_instr_mnemonic (IS_SSE2_SIMD Maskmovdqu) = "IS_SSE2_SIMD Maskmovdqu" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Movdq2q) = "IS_SSE2_SIMD Movdq2q" |  toString_instr_mnemonic (IS_SSE2_SIMD Movdqa) = "IS_SSE2_SIMD Movdqa" |  toString_instr_mnemonic (IS_SSE2_SIMD Movdqu) = "IS_SSE2_SIMD Movdqu" |  toString_instr_mnemonic (IS_SSE2_SIMD Movq2dq) = "IS_SSE2_SIMD Movq2dq" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Movntdq) = "IS_SSE2_SIMD Movntdq" |  toString_instr_mnemonic (IS_SSE2_SIMD Pshufhw) = "IS_SSE2_SIMD Pshufhw" |  toString_instr_mnemonic (IS_SSE2_SIMD Pshuflw) = "IS_SSE2_SIMD Pshuflw" |  toString_instr_mnemonic (IS_SSE2_SIMD Pshufd) = "IS_SSE2_SIMD Pshufd" 
|  toString_instr_mnemonic (IS_SSE2_SIMD Pslldq) = "IS_SSE2_SIMD Pslldq" |  toString_instr_mnemonic (IS_SSE2_SIMD Psrldq) = "IS_SSE2_SIMD Psrldq" |  toString_instr_mnemonic (IS_SSE2_SIMD Punpckhqdq) = "IS_SSE2_SIMD Punpckhqdq" |  toString_instr_mnemonic (IS_SSE2_SIMD Punpcklqdq) = "IS_SSE2_SIMD Punpcklqdq" |

  toString_instr_mnemonic (IS_X86_64 Cdqe) = "IS_X86_64 Cdqe" |  toString_instr_mnemonic (IS_X86_64 Cqo) = "IS_X86_64 Cqo" |  toString_instr_mnemonic (IS_X86_64 Cmpsq) = "IS_X86_64 Cmpsq" |  toString_instr_mnemonic (IS_X86_64 Cmpxchg16b) = "IS_X86_64 Cmpxchg16b" |  toString_instr_mnemonic (IS_X86_64 Iretq) = "IS_X86_64 Iretq" 
|  toString_instr_mnemonic (IS_X86_64 Jrcxz) = "IS_X86_64 Jrcxz" |  toString_instr_mnemonic (IS_X86_64 Lodsq) = "IS_X86_64 Lodsq" |  toString_instr_mnemonic (IS_X86_64 Movsxd) = "IS_X86_64 Movsxd" |  toString_instr_mnemonic (IS_X86_64 Popfq) = "IS_X86_64 Popfq" |  toString_instr_mnemonic (IS_X86_64 Pushfq) = "IS_X86_64 Pushfq" 
|  toString_instr_mnemonic (IS_X86_64 Rdtscp) = "IS_X86_64 Rdtscp" |  toString_instr_mnemonic (IS_X86_64 Scasq) = "IS_X86_64 Scasq" |  toString_instr_mnemonic (IS_X86_64 Stosq) = "IS_X86_64 Stosq" |  toString_instr_mnemonic (IS_X86_64 Swapgs) = "IS_X86_64 Swapgs" |

  toString_instr_mnemonic (IS_SSE3 Monitor) = "IS_SSE3 Monitor" |  toString_instr_mnemonic (IS_SSE3 Mwait) = "IS_SSE3 Mwait" |

  toString_instr_mnemonic (IS_SSE3_x87 Fisttp) = "IS_SSE3_x87 Fisttp" |

  toString_instr_mnemonic (IS_SSE3_SIMD Addsubps) = "IS_SSE3_SIMD Addsubps" |  toString_instr_mnemonic (IS_SSE3_SIMD Addsubpd) = "IS_SSE3_SIMD Addsubpd" |  toString_instr_mnemonic (IS_SSE3_SIMD Movddup) = "IS_SSE3_SIMD Movddup" |  toString_instr_mnemonic (IS_SSE3_SIMD Movsldup) = "IS_SSE3_SIMD Movsldup" 
|  toString_instr_mnemonic (IS_SSE3_SIMD Movshdup) = "IS_SSE3_SIMD Movshdup" |  toString_instr_mnemonic (IS_SSE3_SIMD Haddps) = "IS_SSE3_SIMD Haddps" |  toString_instr_mnemonic (IS_SSE3_SIMD Haddpd) = "IS_SSE3_SIMD Haddpd" |  toString_instr_mnemonic (IS_SSE3_SIMD Hsubps) = "IS_SSE3_SIMD Hsubps" 
|  toString_instr_mnemonic (IS_SSE3_SIMD Hsubpd) = "IS_SSE3_SIMD Hsubpd" |  toString_instr_mnemonic (IS_SSE3_SIMD Lddqu) = "IS_SSE3_SIMD Lddqu" |

  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Psignb) = "IS_SSSE3_SIMDMMX Psignb" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Psignw) = "IS_SSSE3_SIMDMMX Psignw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Psignd) = "IS_SSSE3_SIMDMMX Psignd" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pshufb) = "IS_SSSE3_SIMDMMX Pshufb" 
|  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pmulhrsw) = "IS_SSSE3_SIMDMMX Pmulhrsw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pmaddubsw) = "IS_SSSE3_SIMDMMX Pmaddubsw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubw) = "IS_SSSE3_SIMDMMX Phsubw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubsw) = "IS_SSSE3_SIMDMMX Phsubsw" 
|  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phsubd) = "IS_SSSE3_SIMDMMX Phsubd" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddsw) = "IS_SSSE3_SIMDMMX Phaddsw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddw) = "IS_SSSE3_SIMDMMX Phaddw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Phaddd) = "IS_SSSE3_SIMDMMX Phaddd" 
|  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Palignr) = "IS_SSSE3_SIMDMMX Palignr" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsb) = "IS_SSSE3_SIMDMMX Pabsb" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsw) = "IS_SSSE3_SIMDMMX Pabsw" |  toString_instr_mnemonic (IS_SSSE3_SIMDMMX Pabsd) = "IS_SSSE3_SIMDMMX Pabsd" |

  toString_instr_mnemonic (IS_SSE4_1_SIMD Dpps) = "IS_SSE4_1_SIMD Dpps" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Dppd) = "IS_SSE4_1_SIMD Dppd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Blendps) = "IS_SSE4_1_SIMD Blendps" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Blendvps) = "IS_SSE4_1_SIMD Blendvps" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Blendpd) = "IS_SSE4_1_SIMD Blendpd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Blendvpd) = "IS_SSE4_1_SIMD Blendvpd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Roundps) = "IS_SSE4_1_SIMD Roundps" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Roundss) = "IS_SSE4_1_SIMD Roundss" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Roundpd) = "IS_SSE4_1_SIMD Roundpd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Roundsd) = "IS_SSE4_1_SIMD Roundsd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Insertps) = "IS_SSE4_1_SIMD Insertps" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Extractps) = "IS_SSE4_1_SIMD Extractps" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Mpsadbw) = "IS_SSE4_1_SIMD Mpsadbw" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Phminposuw) = "IS_SSE4_1_SIMD Phminposuw" |   toString_instr_mnemonic (IS_SSE4_1_SIMD Pmulld) = "IS_SSE4_1_SIMD Pmulld" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmuldq) = "IS_SSE4_1_SIMD Pmuldq" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pblendvb) = "IS_SSE4_1_SIMD Pblendvb" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pblendw) = "IS_SSE4_1_SIMD Pblendw" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pminsb) = "IS_SSE4_1_SIMD Pminsb" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pminuw) = "IS_SSE4_1_SIMD Pminuw" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pminsd) = "IS_SSE4_1_SIMD Pminsd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pminud) = "IS_SSE4_1_SIMD Pminud" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmaxsb) = "IS_SSE4_1_SIMD Pmaxsb" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmaxuw) = "IS_SSE4_1_SIMD Pmaxuw" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmaxsd) = "IS_SSE4_1_SIMD Pmaxsd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmaxud) = "IS_SSE4_1_SIMD Pmaxud" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pinsrb) = "IS_SSE4_1_SIMD Pinsrb" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pinsrd) = "IS_SSE4_1_SIMD Pinsrd" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pinsrq) = "IS_SSE4_1_SIMD Pinsrq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pextrb) = "IS_SSE4_1_SIMD Pextrb" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pextrd) = "IS_SSE4_1_SIMD Pextrd" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pextrq) = "IS_SSE4_1_SIMD Pextrq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbw) = "IS_SSE4_1_SIMD Pmovsxbw" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbw) = "IS_SSE4_1_SIMD Pmovzxbw" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbd) = "IS_SSE4_1_SIMD Pmovsxbd" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbd) = "IS_SSE4_1_SIMD Pmovzxbd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxbq) = "IS_SSE4_1_SIMD Pmovsxbq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxbq) = "IS_SSE4_1_SIMD Pmovzxbq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxwd) = "IS_SSE4_1_SIMD Pmovsxwd" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxwd) = "IS_SSE4_1_SIMD Pmovzxwd" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxwq) = "IS_SSE4_1_SIMD Pmovsxwq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxwq) = "IS_SSE4_1_SIMD Pmovzxwq" |   toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovsxdq) = "IS_SSE4_1_SIMD Pmovsxdq" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Pmovzxdq) = "IS_SSE4_1_SIMD Pmovzxdq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Ptest) = "IS_SSE4_1_SIMD Ptest" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Pcmpeqq) = "IS_SSE4_1_SIMD Pcmpeqq" |  toString_instr_mnemonic (IS_SSE4_1_SIMD Packusdw) = "IS_SSE4_1_SIMD Packusdw" 
|  toString_instr_mnemonic (IS_SSE4_1_SIMD Movntdqa) = "IS_SSE4_1_SIMD Movntdqa" |

  toString_instr_mnemonic (IS_VT_X Vmptrld) = "IS_VT_X Vmptrld" |  toString_instr_mnemonic (IS_VT_X Vmptrst) = "IS_VT_X Vmptrst" |  toString_instr_mnemonic (IS_VT_X Vmclear) = "IS_VT_X Vmclear" |  toString_instr_mnemonic (IS_VT_X Vmread) = "IS_VT_X Vmread" |  toString_instr_mnemonic (IS_VT_X Vmwrite) = "IS_VT_X Vmwrite" 
|  toString_instr_mnemonic (IS_VT_X Vmcall) = "IS_VT_X Vmcall" |  toString_instr_mnemonic (IS_VT_X Vmlaunch) = "IS_VT_X Vmlaunch" |  toString_instr_mnemonic (IS_VT_X Vmresume) = "IS_VT_X Vmresume" |  toString_instr_mnemonic (IS_VT_X Vmxoff) = "IS_VT_X Vmxoff" |  toString_instr_mnemonic (IS_VT_X Vmxon) = "IS_VT_X Vmxon" 
|  toString_instr_mnemonic (IS_VT_X Vmfunc) = "IS_VT_X Vmfunc" |  toString_instr_mnemonic (IS_VT_X Invvpid) = "IS_VT_X Invvpid" |  toString_instr_mnemonic (IS_VT_X Invvpid) = "IS_VT_X Invvpid" |

  toString_instr_mnemonic (IS_SSE4_2 Crc32) = "IS_SSE4_2 Crc32" |  toString_instr_mnemonic (IS_SSE4_2 Popcnt) = "IS_SSE4_2 Popcnt" |

  toString_instr_mnemonic (IS_SSE4_2_SIMD Pcmpestri) = "IS_SSE4_2_SIMD Pcmpestri" |  toString_instr_mnemonic (IS_SSE4_2_SIMD Pcmpestrm) = "IS_SSE4_2_SIMD Pcmpestrm" |  toString_instr_mnemonic (IS_SSE4_2_SIMD Pcmpistri) = "IS_SSE4_2_SIMD Pcmpistri" |  toString_instr_mnemonic (IS_SSE4_2_SIMD Pcmpistrm) = "IS_SSE4_2_SIMD Pcmpistrm" 
|  toString_instr_mnemonic (IS_SSE4_2_SIMD Pcmpgtq) = "IS_SSE4_2_SIMD Pcmpgtq" |

  toString_instr_mnemonic (IS_AVX Vsqrtps) = "IS_AVX Vsqrtps" |  toString_instr_mnemonic (IS_AVX Vsqrtpd) = "IS_AVX Vsqrtpd" |  toString_instr_mnemonic (IS_AVX Vrsqrtps) = "IS_AVX Vrsqrtps" |  toString_instr_mnemonic (IS_AVX Vrcpps) = "IS_AVX Vrcpps" |  toString_instr_mnemonic (IS_AVX Vaddps) = "IS_AVX Vaddps" 
|  toString_instr_mnemonic (IS_AVX Vaddpd) = "IS_AVX Vaddpd" |  toString_instr_mnemonic (IS_AVX Vsubps) = "IS_AVX Vsubps" |  toString_instr_mnemonic (IS_AVX Vsubpd) = "IS_AVX Vsubpd" |  toString_instr_mnemonic (IS_AVX Vmulps) = "IS_AVX Vmulps" |  toString_instr_mnemonic (IS_AVX Vmulpd) = "IS_AVX Vmulpd" 
|  toString_instr_mnemonic (IS_AVX Vdivps) = "IS_AVX Vdivps" |  toString_instr_mnemonic (IS_AVX Vdivpd) = "IS_AVX Vdivpd" |  toString_instr_mnemonic (IS_AVX Vcvtps2pd) = "IS_AVX Vcvtps2pd" |  toString_instr_mnemonic (IS_AVX Vcvtpd2ps) = "IS_AVX Vcvtpd2ps" |  toString_instr_mnemonic (IS_AVX Vcvtdq2ps) = "IS_AVX Vcvtdq2ps" 
|  toString_instr_mnemonic (IS_AVX Vcvtps2dq) = "IS_AVX Vcvtps2dq" |  toString_instr_mnemonic (IS_AVX Vcvttps2dq) = "IS_AVX Vcvttps2dq" |  toString_instr_mnemonic (IS_AVX Vcvttpd2dq) = "IS_AVX Vcvttpd2dq" |  toString_instr_mnemonic (IS_AVX Vcvtpd2dq) = "IS_AVX Vcvtpd2dq" 
|  toString_instr_mnemonic (IS_AVX Vcvtdq2pd) = "IS_AVX Vcvtdq2pd" |  toString_instr_mnemonic (IS_AVX Vminps) = "IS_AVX Vminps" |  toString_instr_mnemonic (IS_AVX Vminpd) = "IS_AVX Vminpd" |  toString_instr_mnemonic (IS_AVX Vmaxps) = "IS_AVX Vmaxps" |  toString_instr_mnemonic (IS_AVX Vmaxpd) = "IS_AVX Vmaxpd" 
|  toString_instr_mnemonic (IS_AVX Vhaddpd) = "IS_AVX Vhaddpd" |  toString_instr_mnemonic (IS_AVX Vhaddps) = "IS_AVX Vhaddps" |  toString_instr_mnemonic (IS_AVX Vhsubpd) = "IS_AVX Vhsubpd" |  toString_instr_mnemonic (IS_AVX Vhsubps) = "IS_AVX Vhsubps" |  toString_instr_mnemonic (IS_AVX Vcmpps) = "IS_AVX Vcmpps" 
|  toString_instr_mnemonic (IS_AVX Vcmppd) = "IS_AVX Vcmppd" |  toString_instr_mnemonic (IS_AVX Vaddsubpd) = "IS_AVX Vaddsubpd" |  toString_instr_mnemonic (IS_AVX Vaddsubps) = "IS_AVX Vaddsubps" |  toString_instr_mnemonic (IS_AVX Vdpps) = "IS_AVX Vdpps" |  toString_instr_mnemonic (IS_AVX Vroundpd) = "IS_AVX Vroundpd" 
|  toString_instr_mnemonic (IS_AVX Vroundps) = "IS_AVX Vroundps" |  toString_instr_mnemonic (IS_AVX Vmovaps) = "IS_AVX Vmovaps" |  toString_instr_mnemonic (IS_AVX Vmovapd) = "IS_AVX Vmovapd" |  toString_instr_mnemonic (IS_AVX Vmovdqa) = "IS_AVX Vmovdqa" |  toString_instr_mnemonic (IS_AVX Vmovups) = "IS_AVX Vmovups" 
|  toString_instr_mnemonic (IS_AVX Vmovupd) = "IS_AVX Vmovupd" |  toString_instr_mnemonic (IS_AVX Vmovdqu) = "IS_AVX Vmovdqu" |  toString_instr_mnemonic (IS_AVX Vmovmskps) = "IS_AVX Vmovmskps" |  toString_instr_mnemonic (IS_AVX Vmovmskpd) = "IS_AVX Vmovmskpd" |   toString_instr_mnemonic (IS_AVX Vlddqu) = "IS_AVX Vlddqu" 
|  toString_instr_mnemonic (IS_AVX Vmovntps) = "IS_AVX Vmovntps" |  toString_instr_mnemonic (IS_AVX Vmovntpd) = "IS_AVX Vmovntpd" |  toString_instr_mnemonic (IS_AVX Vmovntdq) = "IS_AVX Vmovntdq" |  toString_instr_mnemonic (IS_AVX Vmovntdqa) = "IS_AVX Vmovntdqa" |  toString_instr_mnemonic (IS_AVX Vmovshdup) = "IS_AVX Vmovshdup" 
|  toString_instr_mnemonic (IS_AVX Vmovsldup) = "IS_AVX Vmovsldup" |  toString_instr_mnemonic (IS_AVX Vmovddup) = "IS_AVX Vmovddup" |  toString_instr_mnemonic (IS_AVX Vunpckhpd) = "IS_AVX Vunpckhpd" |  toString_instr_mnemonic (IS_AVX Vunpckhps) = "IS_AVX Vunpckhps" |  toString_instr_mnemonic (IS_AVX Vunpcklpd) = "IS_AVX Vunpcklpd" 
|  toString_instr_mnemonic (IS_AVX Vblendps) = "IS_AVX Vblendps" |  toString_instr_mnemonic (IS_AVX Vblendpd) = "IS_AVX Vblendpd" |   toString_instr_mnemonic (IS_AVX Vshufpd) = "IS_AVX Vshufpd" |  toString_instr_mnemonic (IS_AVX Vshufps) = "IS_AVX Vshufps" |  toString_instr_mnemonic (IS_AVX Vunpcklps) = "IS_AVX Vunpcklps" 
|  toString_instr_mnemonic (IS_AVX Vblendvps) = "IS_AVX Vblendvps" |  toString_instr_mnemonic (IS_AVX Vblendvpd) = "IS_AVX Vblendvpd" |  toString_instr_mnemonic (IS_AVX Vptest) = "IS_AVX Vptest" |  toString_instr_mnemonic (IS_AVX Vxorps) = "IS_AVX Vxorps" |  toString_instr_mnemonic (IS_AVX Vxorpd) = "IS_AVX Vxorpd" 
|  toString_instr_mnemonic (IS_AVX Vorps) = "IS_AVX Vorps" |  toString_instr_mnemonic (IS_AVX Vorpd) = "IS_AVX Vorpd" |  toString_instr_mnemonic (IS_AVX Vandnpd) = "IS_AVX Vandnpd" |  toString_instr_mnemonic (IS_AVX Vandnps) = "IS_AVX Vandnps" |  toString_instr_mnemonic (IS_AVX Vandpd) = "IS_AVX Vandpd" |  toString_instr_mnemonic (IS_AVX Vandps) = "IS_AVX Vandps" 
|  toString_instr_mnemonic (IS_AVX Vbroadcastf128) = "IS_AVX Vbroadcastf128" |  toString_instr_mnemonic (IS_AVX Vbroadcastsd) = "IS_AVX Vbroadcastsd" |  toString_instr_mnemonic (IS_AVX Vbroadcastss) = "IS_AVX Vbroadcastss" |  toString_instr_mnemonic (IS_AVX Vextractf128) = "IS_AVX Vextractf128" 
|  toString_instr_mnemonic (IS_AVX Vinsertf128) = "IS_AVX Vinsertf128" |  toString_instr_mnemonic (IS_AVX Vmaskmovps) = "IS_AVX Vmaskmovps" |  toString_instr_mnemonic (IS_AVX Vmaskmovpd) = "IS_AVX Vmaskmovpd" |  toString_instr_mnemonic (IS_AVX Vpermilpd) = "IS_AVX Vpermilpd" 
|  toString_instr_mnemonic (IS_AVX Vpermilps) = "IS_AVX Vpermilps" |  toString_instr_mnemonic (IS_AVX Vperm2f128) = "IS_AVX Vperm2f128" |   toString_instr_mnemonic (IS_AVX Vtestps) = "IS_AVX Vtestps" |  toString_instr_mnemonic (IS_AVX Vtestpd) = "IS_AVX Vtestpd" |  toString_instr_mnemonic (IS_AVX Vzeroall) = "IS_AVX Vzeroall" 
|  toString_instr_mnemonic (IS_AVX Vzeroupper) = "IS_AVX Vzeroupper" |  toString_instr_mnemonic (IS_AVX Vcvtsi2ss) = "IS_AVX Vcvtsi2ss" |  toString_instr_mnemonic (IS_AVX Vcvtsi2sd) = "IS_AVX Vcvtsi2sd" |  toString_instr_mnemonic (IS_AVX Vcvtsd2si) = "IS_AVX Vcvtsd2si" 
|  toString_instr_mnemonic (IS_AVX Vcvttss2si) = "IS_AVX Vcvttss2si" |  toString_instr_mnemonic (IS_AVX Vcvttsd2si) = "IS_AVX Vcvttsd2si" |  toString_instr_mnemonic (IS_AVX Vcvtss2si) = "IS_AVX Vcvtss2si" |  toString_instr_mnemonic (IS_AVX Vcomisd) = "IS_AVX Vcomisd" |  toString_instr_mnemonic (IS_AVX Vrsqrtss) = "IS_AVX Vrsqrtss" 
|   toString_instr_mnemonic (IS_AVX Vrcpss) = "IS_AVX Vrcpss" |  toString_instr_mnemonic (IS_AVX Vucomiss) = "IS_AVX Vucomiss" |  toString_instr_mnemonic (IS_AVX Vucomisd) = "IS_AVX Vucomisd" |  toString_instr_mnemonic (IS_AVX Vcomiss) = "IS_AVX Vcomiss" |  toString_instr_mnemonic (IS_AVX Vaddss) = "IS_AVX Vaddss" 
|  toString_instr_mnemonic (IS_AVX Vaddsd) = "IS_AVX Vaddsd" |  toString_instr_mnemonic (IS_AVX Vsubss) = "IS_AVX Vsubss" |  toString_instr_mnemonic (IS_AVX Vsubsd) = "IS_AVX Vsubsd" |  toString_instr_mnemonic (IS_AVX Vmulss) = "IS_AVX Vmulss" |  toString_instr_mnemonic (IS_AVX Vmulsd) = "IS_AVX Vmulsd" |  toString_instr_mnemonic (IS_AVX Vdivss) = "IS_AVX Vdivss" 
|  toString_instr_mnemonic (IS_AVX Vdivsd) = "IS_AVX Vdivsd" |  toString_instr_mnemonic (IS_AVX Vsqrtss) = "IS_AVX Vsqrtss" |  toString_instr_mnemonic (IS_AVX Vsqrtsd) = "IS_AVX Vsqrtsd" |  toString_instr_mnemonic (IS_AVX Vcvtss2sd) = "IS_AVX Vcvtss2sd" |   toString_instr_mnemonic (IS_AVX Vcvtsd2ss) = "IS_AVX Vcvtsd2ss" 
|  toString_instr_mnemonic (IS_AVX Vminss) = "IS_AVX Vminss" |  toString_instr_mnemonic (IS_AVX Vminsd) = "IS_AVX Vminsd" |  toString_instr_mnemonic (IS_AVX Vmaxss) = "IS_AVX Vmaxss" |  toString_instr_mnemonic (IS_AVX Vmaxsd) = "IS_AVX Vmaxsd" |  toString_instr_mnemonic (IS_AVX Vpand) = "IS_AVX Vpand" |  toString_instr_mnemonic (IS_AVX Vpandn) = "IS_AVX Vpandn" 
|  toString_instr_mnemonic (IS_AVX Vpor) = "IS_AVX Vpor" |  toString_instr_mnemonic (IS_AVX Vpxor) = "IS_AVX Vpxor" |  toString_instr_mnemonic (IS_AVX Vpcmpgtb) = "IS_AVX Vpcmpgtb" |  toString_instr_mnemonic (IS_AVX Vpcmpgtw) = "IS_AVX Vpcmpgtw" |  toString_instr_mnemonic (IS_AVX Vpcmpgtd) = "IS_AVX Vpcmpgtd" 
|  toString_instr_mnemonic (IS_AVX Vpmaddwd) = "IS_AVX Vpmaddwd" |  toString_instr_mnemonic (IS_AVX Vpmaddubsw) = "IS_AVX Vpmaddubsw" |  toString_instr_mnemonic (IS_AVX Vpavgb) = "IS_AVX Vpavgb" |   toString_instr_mnemonic (IS_AVX Vpavgw) = "IS_AVX Vpavgw" |  toString_instr_mnemonic (IS_AVX Vpmuludq) = "IS_AVX Vpmuludq" 
|  toString_instr_mnemonic (IS_AVX Vpcmpeqb) = "IS_AVX Vpcmpeqb" |  toString_instr_mnemonic (IS_AVX Vpcmpeqw) = "IS_AVX Vpcmpeqw" |  toString_instr_mnemonic (IS_AVX Vpcmpeqd) = "IS_AVX Vpcmpeqd" |  toString_instr_mnemonic (IS_AVX Vpmullw) = "IS_AVX Vpmullw" |  toString_instr_mnemonic (IS_AVX Vpmulhuw) = "IS_AVX Vpmulhuw" 
|  toString_instr_mnemonic (IS_AVX Vpmulhw) = "IS_AVX Vpmulhw" |  toString_instr_mnemonic (IS_AVX Vpsubsw) = "IS_AVX Vpsubsw" | 

 toString_instr_mnemonic (IS_AVX_2 Vpaddsw) = "IS_AVX_2 Vpaddsw" |  toString_instr_mnemonic (IS_AVX_2 Vpsadbw) = "IS_AVX_2 Vpsadbw" |  toString_instr_mnemonic (IS_AVX_2 Vpaddusb) = "IS_AVX_2 Vpaddusb" |  toString_instr_mnemonic (IS_AVX_2 Vpaddusw) = "IS_AVX_2 Vpaddusw" |  toString_instr_mnemonic (IS_AVX_2 Vpaddsb) = "IS_AVX_2 Vpaddsb" 
|  toString_instr_mnemonic (IS_AVX_2 Vpsubusb) = "IS_AVX_2 Vpsubusb" |  toString_instr_mnemonic (IS_AVX_2 Vpsubusw) = "IS_AVX_2 Vpsubusw" |  toString_instr_mnemonic (IS_AVX_2 Vpsubsb) = "IS_AVX_2 Vpsubsb" |  toString_instr_mnemonic (IS_AVX_2 Vpminub) = "IS_AVX_2 Vpminub" |  toString_instr_mnemonic (IS_AVX_2 Vpminsw) = "IS_AVX_2 Vpminsw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmaxub) = "IS_AVX_2 Vpmaxub" |  toString_instr_mnemonic (IS_AVX_2 Vpmaxsw) = "IS_AVX_2 Vpmaxsw" |  toString_instr_mnemonic (IS_AVX_2 Vpaddb) = "IS_AVX_2 Vpaddb" |  toString_instr_mnemonic (IS_AVX_2 Vpaddw) = "IS_AVX_2 Vpaddw" |  toString_instr_mnemonic (IS_AVX_2 Vpaddd) = "IS_AVX_2 Vpaddd" 
|  toString_instr_mnemonic (IS_AVX_2 Vpaddq) = "IS_AVX_2 Vpaddq" |  toString_instr_mnemonic (IS_AVX_2 Vpsubb) = "IS_AVX_2 Vpsubb" |  toString_instr_mnemonic (IS_AVX_2 Vpsubw) = "IS_AVX_2 Vpsubw" |  toString_instr_mnemonic (IS_AVX_2 Vpsubd) = "IS_AVX_2 Vpsubd" |  toString_instr_mnemonic (IS_AVX_2 Vpsubq) = "IS_AVX_2 Vpsubq" 
|  toString_instr_mnemonic (IS_AVX_2 Vpsllw) = "IS_AVX_2 Vpsllw" |  toString_instr_mnemonic (IS_AVX_2 Vpslld) = "IS_AVX_2 Vpslld" |  toString_instr_mnemonic (IS_AVX_2 Vpsllq) = "IS_AVX_2 Vpsllq" |  toString_instr_mnemonic (IS_AVX_2 Vpsraw) = "IS_AVX_2 Vpsraw" |  toString_instr_mnemonic (IS_AVX_2 Vpsrlw) = "IS_AVX_2 Vpsrlw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpsrld) = "IS_AVX_2 Vpsrld" |  toString_instr_mnemonic (IS_AVX_2 Vpsrlq) = "IS_AVX_2 Vpsrlq" |  toString_instr_mnemonic (IS_AVX_2 Vpsrad) = "IS_AVX_2 Vpsrad" |  toString_instr_mnemonic (IS_AVX_2 Vphsubw) = "IS_AVX_2 Vphsubw" |  toString_instr_mnemonic (IS_AVX_2 Vphsubd) = "IS_AVX_2 Vphsubd" 
|  toString_instr_mnemonic (IS_AVX_2 Vphsubsw) = "IS_AVX_2 Vphsubsw" |   toString_instr_mnemonic (IS_AVX_2 Vphaddw) = "IS_AVX_2 Vphaddw" |  toString_instr_mnemonic (IS_AVX_2 Vphaddd) = "IS_AVX_2 Vphaddd" |  toString_instr_mnemonic (IS_AVX_2 Vphaddsw) = "IS_AVX_2 Vphaddsw" |  toString_instr_mnemonic (IS_AVX_2 Vpmulhrsw) = "IS_AVX_2 Vpmulhrsw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpsignb) = "IS_AVX_2 Vpsignb" |  toString_instr_mnemonic (IS_AVX_2 Vpsignw) = "IS_AVX_2 Vpsignw" |  toString_instr_mnemonic (IS_AVX_2 Vpsignd) = "IS_AVX_2 Vpsignd" |  toString_instr_mnemonic (IS_AVX_2 Vpabsb) = "IS_AVX_2 Vpabsb" |  toString_instr_mnemonic (IS_AVX_2 Vpabsw) = "IS_AVX_2 Vpabsw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpabsd) = "IS_AVX_2 Vpabsd" |  toString_instr_mnemonic (IS_AVX_2 Vdppd) = "IS_AVX_2 Vdppd" |  toString_instr_mnemonic (IS_AVX_2 Vphminposuw) = "IS_AVX_2 Vphminposuw" |  toString_instr_mnemonic (IS_AVX_2 Vmpsadbw) = "IS_AVX_2 Vmpsadbw" |  toString_instr_mnemonic (IS_AVX_2 Vpmaxsb) = "IS_AVX_2 Vpmaxsb" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmaxsd) = "IS_AVX_2 Vpmaxsd" |   toString_instr_mnemonic (IS_AVX_2 Vpmaxud) = "IS_AVX_2 Vpmaxud" |  toString_instr_mnemonic (IS_AVX_2 Vpminsb) = "IS_AVX_2 Vpminsb" |  toString_instr_mnemonic (IS_AVX_2 Vpminsd) = "IS_AVX_2 Vpminsd" |  toString_instr_mnemonic (IS_AVX_2 Vpminud) = "IS_AVX_2 Vpminud" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmaxuw) = "IS_AVX_2 Vpmaxuw" |  toString_instr_mnemonic (IS_AVX_2 Vpminuw) = "IS_AVX_2 Vpminuw" |  toString_instr_mnemonic (IS_AVX_2 Vpmovsxbw) = "IS_AVX_2 Vpmovsxbw" |  toString_instr_mnemonic (IS_AVX_2 Vpmovzxbw) = "IS_AVX_2 Vpmovzxbw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmovsxbd) = "IS_AVX_2 Vpmovsxbd" |  toString_instr_mnemonic (IS_AVX_2 Vpmovzxbd) = "IS_AVX_2 Vpmovzxbd" |  toString_instr_mnemonic (IS_AVX_2 Vpmovsxbq) = "IS_AVX_2 Vpmovsxbq" |  toString_instr_mnemonic (IS_AVX_2 Vpmovzxbq) = "IS_AVX_2 Vpmovzxbq" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmovsxwd) = "IS_AVX_2 Vpmovsxwd" |   toString_instr_mnemonic (IS_AVX_2 Vpmovzxwd) = "IS_AVX_2 Vpmovzxwd" |  toString_instr_mnemonic (IS_AVX_2 Vpmovsxwq) = "IS_AVX_2 Vpmovsxwq" |  toString_instr_mnemonic (IS_AVX_2 Vpmovzxwq) = "IS_AVX_2 Vpmovzxwq" 
|  toString_instr_mnemonic (IS_AVX_2 Vpmovsxdq) = "IS_AVX_2 Vpmovsxdq" |  toString_instr_mnemonic (IS_AVX_2 Vpmovzxdq) = "IS_AVX_2 Vpmovzxdq" |  toString_instr_mnemonic (IS_AVX_2 Vpmuldq) = "IS_AVX_2 Vpmuldq" |  toString_instr_mnemonic (IS_AVX_2 Vpmulld) = "IS_AVX_2 Vpmulld" |  toString_instr_mnemonic (IS_AVX_2 Vroundsd) = "IS_AVX_2 Vroundsd" 
|  toString_instr_mnemonic (IS_AVX_2 Vroundss) = "IS_AVX_2 Vroundss" |  toString_instr_mnemonic (IS_AVX_2 Vpopcnt) = "IS_AVX_2 Vpopcnt" |  toString_instr_mnemonic (IS_AVX_2 Vpcmpgtq) = "IS_AVX_2 Vpcmpgtq" |  toString_instr_mnemonic (IS_AVX_2 Vpcmpestri) = "IS_AVX_2 Vpcmpestri" 
|  toString_instr_mnemonic (IS_AVX_2 Vpcmpestrm) = "IS_AVX_2 Vpcmpestrm" |   toString_instr_mnemonic (IS_AVX_2 Vpcmpistri) = "IS_AVX_2 Vpcmpistri" |  toString_instr_mnemonic (IS_AVX_2 Vpcmpistrm) = "IS_AVX_2 Vpcmpistrm" |  toString_instr_mnemonic (IS_AVX_2 Vpclmulqdq) = "IS_AVX_2 Vpclmulqdq" 
|  toString_instr_mnemonic (IS_AVX_2 Vaesdec) = "IS_AVX_2 Vaesdec" |  toString_instr_mnemonic (IS_AVX_2 Vaesdeclast) = "IS_AVX_2 Vaesdeclast" |  toString_instr_mnemonic (IS_AVX_2 Vaesenc) = "IS_AVX_2 Vaesenc" |  toString_instr_mnemonic (IS_AVX_2 Vaesenclast) = "IS_AVX_2 Vaesenclast" 
|  toString_instr_mnemonic (IS_AVX_2 Vaesimx) = "IS_AVX_2 Vaesimx" |  toString_instr_mnemonic (IS_AVX_2 Vaeskeygenassist) = "IS_AVX_2 Vaeskeygenassist" |  toString_instr_mnemonic (IS_AVX_2 Vstmxcsr) = "IS_AVX_2 Vstmxcsr" |  toString_instr_mnemonic (IS_AVX_2 Vmovss) = "IS_AVX_2 Vmovss" |  toString_instr_mnemonic (IS_AVX_2 Vmovsd) = "IS_AVX_2 Vmovsd" 
|   toString_instr_mnemonic (IS_AVX_2 Vcmpss) = "IS_AVX_2 Vcmpss" |  toString_instr_mnemonic (IS_AVX_2 Vcmpsd) = "IS_AVX_2 Vcmpsd" |  toString_instr_mnemonic (IS_AVX_2 Vmovhps) = "IS_AVX_2 Vmovhps" |  toString_instr_mnemonic (IS_AVX_2 Vmovhpd) = "IS_AVX_2 Vmovhpd" |  toString_instr_mnemonic (IS_AVX_2 Vmovlps) = "IS_AVX_2 Vmovlps" 
|  toString_instr_mnemonic (IS_AVX_2 Vmovlpd) = "IS_AVX_2 Vmovlpd" |  toString_instr_mnemonic (IS_AVX_2 Vmovlhps) = "IS_AVX_2 Vmovlhps" |  toString_instr_mnemonic (IS_AVX_2 Vmovhlps) = "IS_AVX_2 Vmovhlps" |  toString_instr_mnemonic (IS_AVX_2 Vmovq) = "IS_AVX_2 Vmovq" |  toString_instr_mnemonic (IS_AVX_2 Vmovd) = "IS_AVX_2 Vmovd" 
|  toString_instr_mnemonic (IS_AVX_2 Vpackuswb) = "IS_AVX_2 Vpackuswb" |  toString_instr_mnemonic (IS_AVX_2 Vpackssdw) = "IS_AVX_2 Vpackssdw" |  toString_instr_mnemonic (IS_AVX_2 Vpacksswb) = "IS_AVX_2 Vpacksswb" |  toString_instr_mnemonic (IS_AVX_2 Vpunpckhbw) = "IS_AVX_2 Vpunpckhbw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpunpckhwd) = "IS_AVX_2 Vpunpckhwd" |  toString_instr_mnemonic (IS_AVX_2 Vpunpcklbw) = "IS_AVX_2 Vpunpcklbw" |  toString_instr_mnemonic (IS_AVX_2 Vpunpcklwd) = "IS_AVX_2 Vpunpcklwd" |  toString_instr_mnemonic (IS_AVX_2 Vpunpckhdq) = "IS_AVX_2 Vpunpckhdq" 
|  toString_instr_mnemonic (IS_AVX_2 Vpunpckldq) = "IS_AVX_2 Vpunpckldq" |  toString_instr_mnemonic (IS_AVX_2 Vpunpcklqdq) = "IS_AVX_2 Vpunpcklqdq" |  toString_instr_mnemonic (IS_AVX_2 Vpunpckhqdq) = "IS_AVX_2 Vpunpckhqdq" |  toString_instr_mnemonic (IS_AVX_2 Vpshufhw) = "IS_AVX_2 Vpshufhw" 
|  toString_instr_mnemonic (IS_AVX_2 Vpshuflw) = "IS_AVX_2 Vpshuflw" |  toString_instr_mnemonic (IS_AVX_2 Vpshufd) = "IS_AVX_2 Vpshufd" |  toString_instr_mnemonic (IS_AVX_2 Vpmovmskb) = "IS_AVX_2 Vpmovmskb" |   toString_instr_mnemonic (IS_AVX_2 Vmaskmovdqu) = "IS_AVX_2 Vmaskmovdqu" 
|  toString_instr_mnemonic (IS_AVX_2 Vpinsrw) = "IS_AVX_2 Vpinsrw" |  toString_instr_mnemonic (IS_AVX_2 Vpextrw) = "IS_AVX_2 Vpextrw" |  toString_instr_mnemonic (IS_AVX_2 Vpalignr) = "IS_AVX_2 Vpalignr" |  toString_instr_mnemonic (IS_AVX_2 Vpshufb) = "IS_AVX_2 Vpshufb" |  toString_instr_mnemonic (IS_AVX_2 Vextractps) = "IS_AVX_2 Vextractps" 
|  toString_instr_mnemonic (IS_AVX_2 Vinsertps) = "IS_AVX_2 Vinsertps" |  toString_instr_mnemonic (IS_AVX_2 Vpackusdw) = "IS_AVX_2 Vpackusdw" |  toString_instr_mnemonic (IS_AVX_2 Vpcmpeqq) = "IS_AVX_2 Vpcmpeqq" |  toString_instr_mnemonic (IS_AVX_2 Vpblendvb) = "IS_AVX_2 Vpblendvb" 
|  toString_instr_mnemonic (IS_AVX_2 Vpblendw) = "IS_AVX_2 Vpblendw" |  toString_instr_mnemonic (IS_AVX_2 Vpextrb) = "IS_AVX_2 Vpextrb" |   toString_instr_mnemonic (IS_AVX_2 Vpextrd) = "IS_AVX_2 Vpextrd" |  toString_instr_mnemonic (IS_AVX_2 Vpextrq) = "IS_AVX_2 Vpextrq" |  toString_instr_mnemonic (IS_AVX_2 Vpinsrb) = "IS_AVX_2 Vpinsrb" 
|  toString_instr_mnemonic (IS_AVX_2 Vpinsrd) = "IS_AVX_2 Vpinsrd" |  toString_instr_mnemonic (IS_AVX_2 Vpinsrq) = "IS_AVX_2 Vpinsrq" |

  toString_instr_mnemonic (IS_FMA Vfmadd132pd) = "IS_FMA Vfmadd132pd" |  toString_instr_mnemonic (IS_FMA Vfmadd213pd) = "IS_FMA Vfmadd213pd" |  toString_instr_mnemonic (IS_FMA Vfmadd231pd) = "IS_FMA Vfmadd231pd" |  toString_instr_mnemonic (IS_FMA Vfmadd132ps) = "IS_FMA Vfmadd132ps" 
|  toString_instr_mnemonic (IS_FMA Vfmadd213ps) = "IS_FMA Vfmadd213ps" |  toString_instr_mnemonic (IS_FMA Vfmadd231ps) = "IS_FMA Vfmadd231ps" |  toString_instr_mnemonic (IS_FMA Vfmadd132sd) = "IS_FMA Vfmadd132sd" |  toString_instr_mnemonic (IS_FMA Vfmadd213sd) = "IS_FMA Vfmadd213sd" 
|  toString_instr_mnemonic (IS_FMA Vfmadd231sd) = "IS_FMA Vfmadd231sd" |  toString_instr_mnemonic (IS_FMA Vfmadd132ss) = "IS_FMA Vfmadd132ss" |  toString_instr_mnemonic (IS_FMA Vfmadd213ss) = "IS_FMA Vfmadd213ss" |   toString_instr_mnemonic (IS_FMA Vfmadd231ss) = "IS_FMA Vfmadd231ss" 
|  toString_instr_mnemonic (IS_FMA Vfmaddsub132pd) = "IS_FMA Vfmaddsub132pd" |  toString_instr_mnemonic (IS_FMA Vfmaddsub213pd) = "IS_FMA Vfmaddsub213pd" |  toString_instr_mnemonic (IS_FMA Vfmaddsub231pd) = "IS_FMA Vfmaddsub231pd" 
|  toString_instr_mnemonic (IS_FMA Vfmaddsub132ps) = "IS_FMA Vfmaddsub132ps" |  toString_instr_mnemonic (IS_FMA Vfmaddsub213ps) = "IS_FMA Vfmaddsub213ps" |  toString_instr_mnemonic (IS_FMA Vfmaddsub231ps) = "IS_FMA Vfmaddsub231ps" 
|  toString_instr_mnemonic (IS_FMA Vfmsubadd132pd) = "IS_FMA Vfmsubadd132pd" |  toString_instr_mnemonic (IS_FMA Vfmsubadd213pd) = "IS_FMA Vfmsubadd213pd" |   toString_instr_mnemonic (IS_FMA Vfmsubadd231pd) = "IS_FMA Vfmsubadd231pd" 
|  toString_instr_mnemonic (IS_FMA Vfmsubadd132ps) = "IS_FMA Vfmsubadd132ps" |  toString_instr_mnemonic (IS_FMA Vfmsubadd213ps) = "IS_FMA Vfmsubadd213ps" |  toString_instr_mnemonic (IS_FMA Vfmsubadd231ps) = "IS_FMA Vfmsubadd231ps" 
|  toString_instr_mnemonic (IS_FMA Vfmsub132pd) = "IS_FMA Vfmsub132pd" |  toString_instr_mnemonic (IS_FMA Vfmsub213pd) = "IS_FMA Vfmsub213pd" |  toString_instr_mnemonic (IS_FMA Vfmsub231pd) = "IS_FMA Vfmsub231pd" |  toString_instr_mnemonic (IS_FMA Vfmsub132ps) = "IS_FMA Vfmsub132ps" 
|  toString_instr_mnemonic (IS_FMA Vfmsub213ps) = "IS_FMA Vfmsub213ps" |  toString_instr_mnemonic (IS_FMA Vfmsub231ps) = "IS_FMA Vfmsub231ps" |   toString_instr_mnemonic (IS_FMA Vfmsub132sd) = "IS_FMA Vfmsub132sd" |  toString_instr_mnemonic (IS_FMA Vfmsub213sd) = "IS_FMA Vfmsub213sd" 
|  toString_instr_mnemonic (IS_FMA Vfmsub231sd) = "IS_FMA Vfmsub231sd" |  toString_instr_mnemonic (IS_FMA Vfmsub132ss) = "IS_FMA Vfmsub132ss" |  toString_instr_mnemonic (IS_FMA Vfmsub213ss) = "IS_FMA Vfmsub213ss" |  toString_instr_mnemonic (IS_FMA Vfmsub231ss) = "IS_FMA Vfmsub231ss" 
|  toString_instr_mnemonic (IS_FMA Vfnmadd132pd) = "IS_FMA Vfnmadd132pd" |  toString_instr_mnemonic (IS_FMA Vfnmadd213pd) = "IS_FMA Vfnmadd213pd" |  toString_instr_mnemonic (IS_FMA Vfnmadd231pd) = "IS_FMA Vfnmadd231pd" |  toString_instr_mnemonic (IS_FMA Vfnmadd132ps) = "IS_FMA Vfnmadd132ps" 
|   toString_instr_mnemonic (IS_FMA Vfnmadd213ps) = "IS_FMA Vfnmadd213ps" |  toString_instr_mnemonic (IS_FMA Vfnmadd231ps) = "IS_FMA Vfnmadd231ps" |  toString_instr_mnemonic (IS_FMA Vfnmadd132sd) = "IS_FMA Vfnmadd132sd" |  toString_instr_mnemonic (IS_FMA Vfnmadd213sd) = "IS_FMA Vfnmadd213sd" 
|  toString_instr_mnemonic (IS_FMA Vfnmadd231sd) = "IS_FMA Vfnmadd231sd" |  toString_instr_mnemonic (IS_FMA Vfnmadd132ss) = "IS_FMA Vfnmadd132ss" |  toString_instr_mnemonic (IS_FMA Vfnmadd213ss) = "IS_FMA Vfnmadd213ss" |  toString_instr_mnemonic (IS_FMA Vfnmadd231ss) = "IS_FMA Vfnmadd231ss" 
|  toString_instr_mnemonic (IS_FMA Vfnmsub132pd) = "IS_FMA Vfnmsub132pd" |  toString_instr_mnemonic (IS_FMA Vfnmsub213pd) = "IS_FMA Vfnmsub213pd" |   toString_instr_mnemonic (IS_FMA Vfnmsub231pd) = "IS_FMA Vfnmsub231pd" |  toString_instr_mnemonic (IS_FMA Vfnmsub132ps) = "IS_FMA Vfnmsub132ps" 
|  toString_instr_mnemonic (IS_FMA Vfnmsub213ps) = "IS_FMA Vfnmsub213ps" |  toString_instr_mnemonic (IS_FMA Vfnmsub231ps) = "IS_FMA Vfnmsub231ps" |  toString_instr_mnemonic (IS_FMA Vfnmsub132sd) = "IS_FMA Vfnmsub132sd" |  toString_instr_mnemonic (IS_FMA Vfnmsub213sd) = "IS_FMA Vfnmsub213sd" 
|  toString_instr_mnemonic (IS_FMA Vfnmsub231sd) = "IS_FMA Vfnmsub231sd" |  toString_instr_mnemonic (IS_FMA Vfnmsub132ss) = "IS_FMA Vfnmsub132ss" |  toString_instr_mnemonic (IS_FMA Vfnmsub213ss) = "IS_FMA Vfnmsub213ss" |  toString_instr_mnemonic (IS_FMA Vfnmsub231ss) = "IS_FMA Vfnmsub231ss" |

  toString_instr_mnemonic (IS_BM1_BM2 Andn) = "IS_BM1_BM2 Andn" |  toString_instr_mnemonic (IS_BM1_BM2 Bextr) = "IS_BM1_BM2 Bextr" |  toString_instr_mnemonic (IS_BM1_BM2 Blsi) = "IS_BM1_BM2 Blsi" |  toString_instr_mnemonic (IS_BM1_BM2 Blsmsk) = "IS_BM1_BM2 Blsmsk" |  toString_instr_mnemonic (IS_BM1_BM2 Blsr) = "IS_BM1_BM2 Blsr" 
|  toString_instr_mnemonic (IS_BM1_BM2 Bzhi) = "IS_BM1_BM2 Bzhi" |  toString_instr_mnemonic (IS_BM1_BM2 Lzcnt) = "IS_BM1_BM2 Lzcnt" |  toString_instr_mnemonic (IS_BM1_BM2 Mulx) = "IS_BM1_BM2 Mulx" |  toString_instr_mnemonic (IS_BM1_BM2 Pdep) = "IS_BM1_BM2 Pdep" |  toString_instr_mnemonic (IS_BM1_BM2 Pext) = "IS_BM1_BM2 Pext" |  toString_instr_mnemonic (IS_BM1_BM2 Rorx) = "IS_BM1_BM2 Rorx" 
|  toString_instr_mnemonic (IS_BM1_BM2 Sarx) = "IS_BM1_BM2 Sarx" |  toString_instr_mnemonic (IS_BM1_BM2 Shlx) = "IS_BM1_BM2 Shlx" |  toString_instr_mnemonic (IS_BM1_BM2 Shrx) = "IS_BM1_BM2 Shrx" |  toString_instr_mnemonic (IS_BM1_BM2 Tzcnt) = "IS_BM1_BM2 Tzcnt" |
 
  toString_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastb) = "IS_AVX_512_VL_DQ_BW Vpbroadcastb" |  toString_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastd) = "IS_AVX_512_VL_DQ_BW Vpbroadcastd" |  toString_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastq) = "IS_AVX_512_VL_DQ_BW Vpbroadcastq" 
|  toString_instr_mnemonic (IS_AVX_512_VL_DQ_BW Vpbroadcastw) = "IS_AVX_512_VL_DQ_BW Vpbroadcastw" 


(* MNEMONICS END *)

(* INSTRUCTION BEGIN *)

datatype instr =
  Nullary of instr_mnemonic 
| Unary of (instr_mnemonic * operand_src)
| Binary of (instr_mnemonic * operand_dest * operand_src )
| Ternary of (instr_mnemonic * operand_dest * operand_src * operand_src) 

fun mk_instr (Nullary (instr_mnemonic)) = @{term "Nullary"} $ mk_instr_mnemonic instr_mnemonic 
|   mk_instr (Unary   (instr_mnemonic,src)) = @{term "Unary"} $ mk_instr_mnemonic instr_mnemonic $ mk_operand_src src
|   mk_instr (Binary  (instr_mnemonic,dst,src)) = @{term "Binary"} $ mk_instr_mnemonic instr_mnemonic $ mk_operand_dest dst $ mk_operand_src src
|   mk_instr (Ternary  (instr_mnemonic,dst,src1,src2)) = @{term "Ternary"} $ mk_instr_mnemonic instr_mnemonic $ mk_operand_dest dst $ mk_operand_src src1 $ mk_operand_src src2

fun toString_instr (Nullary (nem)) = "Nullary " ^ toString_instr_mnemonic nem
|   toString_instr (Unary (nem,src)) = "Unary " ^ toString_instr_mnemonic nem ^ " " ^ toString_operand_src src
|   toString_instr (Binary (nem,dst,src)) = "Binary " ^ toString_instr_mnemonic nem ^ " " ^ toString_operand_dest dst^ " ," ^ toString_operand_src src
|   toString_instr (Ternary (nem,dst,src1,src2)) = "Ternary " ^ toString_instr_mnemonic nem ^ " " ^ toString_operand_dest dst ^ " ," ^ toString_operand_src src1 ^ " ," ^ toString_operand_src src2

(* INSTRUCTION END *)




(* OPERAND SIG BEGIN *)
datatype operand_sig =
  Nullary_sig  
| Unary_sig of (operand_src_sig)
| Binary_sig of (operand_dest_sig * operand_src_sig )
| Ternary_sig of (operand_dest_sig * operand_src_sig * operand_src_sig) 
(* $ mk_instr_mnemonic instr_mnemonic
^ toString_instr_mnemonic nem
 *)
fun mk_operand_sig (Nullary_sig ) = @{term "Nullary_sig"} 
|   mk_operand_sig (Unary_sig   (src)) = @{term "Unary_sig"} $ mk_operand_src_sig src
|   mk_operand_sig (Binary_sig  (dst,src)) = @{term "Binary_sig"} $ mk_operand_dest_sig dst $ mk_operand_src_sig src
|   mk_operand_sig (Ternary_sig  (dst,src1,src2)) = @{term "Ternary_sig"} $ mk_operand_dest_sig dst $ mk_operand_src_sig src1 $ mk_operand_src_sig src2

fun toString_operand_sig (Nullary_sig) = "[Nullary_sig]"
|   toString_operand_sig (Unary_sig (src)) = "[Unary_sig " ^ toString_operand_src_sig src ^ "]"
|   toString_operand_sig (Binary_sig (dst,src)) = "[Binary_sig " ^ toString_operand_dest_sig dst ^ ", " ^ toString_operand_src_sig src ^ "]"
|   toString_operand_sig (Ternary_sig (dst,src1,src2)) = "[Ternary_sig " ^ toString_operand_dest_sig dst ^ ", " ^ toString_operand_src_sig src1 ^ " ," ^ toString_operand_src_sig src2 ^ "]"

(* OPERAND SIG END *)




(* FLAGS BEGIN *)

fun mk_flg (flag_cf) = @{term flag_cf}
  | mk_flg (flag_sf) = @{term flag_sf}
  | mk_flg (flag_af) = @{term flag_af}
  | mk_flg (flag_of) = @{term flag_of}
  | mk_flg (flag_zf) = @{term flag_zf}
  | mk_flg (flag_pf) = @{term flag_pf}


fun toString_flag (flag_cf) = "CF"
  | toString_flag (flag_zf) = "ZF"
  | toString_flag (flag_of) = "OF"
  | toString_flag (flag_af) = "AF"
  | toString_flag (flag_pf) = "PF"
  | toString_flag (flag_sf) = "SF"

(* FLAGS END *)




datatype text_line =
    Text_Empty
  | Text_Label of string
  | Text_Instr of instr * int

datatype data_value =
    Data_Constant of int * int
  | Data_Var of string * int
  | Data_String of string * int


datatype data_line =
    Data_Empty
  | Data_Label of string
  | Data_Data of data_value

type text_section = {ts_name : string, instructions : (int * instr * int) list}
type build_text_section = (int * text_section * (string * int) list * int)

fun add_text_line Text_Empty (i,ts,label_addresses,offset) = (i,ts,label_addresses,offset)
  | add_text_line (Text_Label l) (i,{ts_name = n, instructions = is},label_addresses,offset) =
      (i,{ts_name = n, instructions = is},(l,offset)::label_addresses,offset)
  | add_text_line (Text_Instr (instr,size)) (i,{ts_name = n, instructions = is},label_addresses,offset) =
      (i+1,{ts_name = n, instructions = is@[(offset,instr,size)]},label_addresses,offset + size)

fun add_text_lines [] x = x
  | add_text_lines (tl::tls) x =
    let val x' = add_text_line tl x in
      add_text_lines tls x'
    end
   
fun build_text_section ((Text_Label s)::ls) =
   add_text_lines ((Text_Label s)::ls) (0,{ts_name = s, instructions = []},[],0)
 | build_text_section ls =
  let val ln = !section_number
      val  _ = section_number := ln+1 in
   add_text_lines ls (0,{ts_name = "unnamed_text_section" ^ toString ln, instructions = []},[],0)
   end


type data_section = { ds_name : string, ds_size : int, ds_data : data_value list }
type build_data_section = (int * data_section * (string * int) list * int)

(* Takes bits l up to (but not including) h of a little-ending encoded int *)
fun take_bits l h i = (i mod (pow(2,h))) div (pow(2,l))

fun data_value_size (Data_Constant (_,s)) = s
  | data_value_size (Data_Var (_,s)) = s
  | data_value_size (Data_String (_,s)) = s

fun add_data_line Data_Empty (i,ds,label_addresses,offset) = (i,ds,label_addresses,offset)
  | add_data_line (Data_Label l) (i,{ds_name = n, ds_size = s, ds_data = ds},label_addresses,offset) =
      (i,{ds_name = n, ds_size = s, ds_data = ds},(l,offset)::label_addresses,offset)
  | add_data_line (Data_Data v) (i,{ds_name = n, ds_size = s, ds_data = d},label_addresses,offset) =
      (i+1,{ds_name = n, ds_size = s+data_value_size v, ds_data = d@[v]},label_addresses,offset + data_value_size v)


fun add_data_lines [] x = x
  | add_data_lines (dl::dls) x =
    let val x' = add_data_line dl x in
      add_data_lines dls x'
    end
    
fun build_data_section ((Data_Label s)::ls) =
   add_data_lines ((Data_Label s)::ls) (0, {ds_name = s, ds_size = 0, ds_data = []},[],0)
 | build_data_section ls =
  let val ln = !section_number
      val  _ = section_number := ln+1 in
    add_data_lines ls (0, {ds_name = "unnamed_data_section" ^ toString ln, ds_size = 0, ds_data = []},[],0)
  end

fun mk_word_typ_from_num s = Syntax.read_typ @{context} ("num \<Rightarrow> " ^ toString s ^ " word")
fun mk_word_typ s = Syntax.read_typ @{context} (toString s ^ " word")

fun mk_word i b = 
            if i=0 then 
              Const ("Groups.zero_class.zero", mk_word_typ b)
            else if i=1 then
              Const ("Groups.one_class.one", mk_word_typ b)
            else
              Const ("Num.numeral_class.numeral", mk_word_typ_from_num b) $ HOLogic.mk_numeral i

fun mk_data_value (Data_Constant (i,1)) = @{term Data_Byte} $ mk_word i 8
  | mk_data_value (Data_Constant (i,8)) = @{term Data_Quad} $ mk_word i 64
  | mk_data_value (Data_Constant (_,s)) = raise TERM ("mk_data_value: unknown data size: " ^ toString s, [])
  | mk_data_value (Data_Var (v,_)) = @{term Data_Var} $ mk_string v
  | mk_data_value (Data_String (v,b)) = @{term Data_String} $ mk_string v $ mk_nat b


type assembly = { 
  instruction_list : (int * instr * int) list,
  data_sections : (int * (data_value list)) list,
  labels_to_addresses : (string * int) list,
	current_offset : int (* the offset of the current section *)
  }

fun update_labels_with_offset _ [] = []
	| update_labels_with_offset offset ((l,offset')::ls) = ((l,offset'+offset)::(update_labels_with_offset offset ls))

fun add_offset_to_text_section_instructions offset (offset',i,size) = (offset+offset',i,size)

fun text_section_to_instruction_list offset {ts_name = _, instructions = is} = map (add_offset_to_text_section_instructions offset) is

fun append_text_section_to_assembly offset ts tss =
	tss@(text_section_to_instruction_list offset ts)

fun get_data_from_data_section {ds_name = _, ds_size = _, ds_data = ds} = ds
fun get_name_from_text_section {ts_name = n, instructions = _} = n

fun add_text_section_to_assembly (_,ts,label_addresses,size) {instruction_list = tss, data_sections = dss, labels_to_addresses = lta, current_offset = offset} =
  let val _ = tracing ("Adding text section " ^ get_name_from_text_section ts ^ ", current offset = " ^ toString offset) in
    {instruction_list = append_text_section_to_assembly offset ts tss, data_sections = dss,
     labels_to_addresses = lta@(update_labels_with_offset offset label_addresses),current_offset = offset + size }
  end

fun add_data_section_to_assembly (_, ds,label_addresses,size) {instruction_list = tss, data_sections = dss, labels_to_addresses = lta, current_offset = offset} =
  let val _ = tracing ("Adding data section, current offset = " ^ toString offset) in
    {instruction_list = tss, data_sections = (offset,get_data_from_data_section ds)::dss,
     labels_to_addresses = lta@(update_labels_with_offset offset label_addresses),current_offset = offset + size}
  end

fun mk_label (l,offset) = HOLogic.mk_prod (mk_string l, mk_nat offset)

fun mk_instruction_list (offset,i,size) = HOLogic.mk_prod (mk_nat offset, HOLogic.mk_prod (mk_instr i, mk_nat size))

fun mk_data_list (offset, dvs) = HOLogic.mk_prod (mk_nat offset, mk_list @{typ "data_value"} (map mk_data_value dvs))

fun mk_assembly { instruction_list = is, data_sections = ds, labels_to_addresses = lta, current_offset = _ } boffset =
  @{term "assembly.make"}
    $ mk_list @{typ "nat \<times> instr \<times> nat"} (map mk_instruction_list is)
    $ mk_list @{typ "nat \<times> (data_value list)"} (map mk_data_list ds)
    $ mk_list @{typ "string \<times> nat"} (map mk_label lta)
		$ boffset
                          
val empty_assembly = {instruction_list = [], data_sections = [], labels_to_addresses = [], current_offset = 0}

fun map_with_index _ _ [] = []
	| map_with_index f i (x::xs) = (f i x)::(map_with_index f (i+1) xs)

fun instr_to_lookup i (offset,_,_) = (offset, i)

fun add_lookup_entry ((offset,i),m) = @{term "fun_upd :: (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> (nat \<Rightarrow> nat option)"}
                                      $ m
                                      $ (mk_nat offset)
                                      $ (@{term "Some :: nat \<Rightarrow> nat option"} $ mk_nat i)

val entrysize = 100

fun in_current_upper_entry current_upper_entry (offset,_,_) = offset < current_upper_entry + entrysize

fun mk_upper_entry is current_upper_entry current_index m =
	let val (is0,is1) = List.partition (in_current_upper_entry current_upper_entry) is
			val lt = map_with_index instr_to_lookup current_index is0
			val new_current_index = current_index + List.length is0
			val e  = @{term "Map.empty :: nat \<rightharpoonup> nat"}
	    val e  = foldl add_lookup_entry e lt
			val m  = @{term "fun_upd :: (nat \<Rightarrow> (nat \<Rightarrow> nat option) option) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat option) option \<Rightarrow> (nat \<Rightarrow> (nat \<Rightarrow> nat option) option)"}
                   $ m
                   $ (mk_nat current_upper_entry)
                   $ (@{term "Some :: (nat \<Rightarrow> nat option) \<Rightarrow> ((nat \<Rightarrow> nat option) option)"} $ e)
		in
			(m,is1,new_current_index)
	end

fun instruction_list_to_lookup_table [] _ _ m = m
	| instruction_list_to_lookup_table is current_upper_entry current_index m =
		let val (m,is1,current_index) = mk_upper_entry is current_upper_entry current_index m in
			instruction_list_to_lookup_table is1 (current_upper_entry + entrysize) current_index m
		end
	
fun mk_lookup_table {instruction_list = is, data_sections = _, labels_to_addresses = _, current_offset = _} =
	let val m = @{term "Map.empty :: nat \<rightharpoonup> (nat \<Rightarrow> nat option)"} in
	    instruction_list_to_lookup_table is 0 0 m
  end

fun toString_instruction_list (offset,i,size) =
		toString offset ^ ": " ^ toString_instr i ^ " (" ^ toString size ^ ")"

fun toString_data_value (Data_Constant (i,b)) = toString i ^ " (" ^ toString b ^ " bytes)"
  | toString_data_value (Data_Var (v,b)) = v ^ " (" ^ toString b ^ " bytes)"
  | toString_data_value (Data_String (v,b)) = v ^ " (" ^ toString b ^ " bytes)"

fun toString_data_section (offset,dvs) =
		toString offset ^ ":\n" ^ intercalate "\n" (map toString_data_value dvs)

fun toString_label (name,offset) = name ^ " --> " ^ toString offset

fun toString_assembly {instruction_list= is, data_sections = dss, labels_to_addresses = lta, current_offset = _  } =
  intercalate "\n"
      (map toString_instruction_list is@["\n"]
      @["Data sections" ]
      @map toString_data_section dss@["\n"]
      @["Labels to addresses" ]
      @map toString_label lta
      )


fun add_newline s = s ^ "\n"
fun add_semicolon s = s ^ " ; "
