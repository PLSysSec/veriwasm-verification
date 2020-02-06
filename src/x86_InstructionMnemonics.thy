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

theory x86_InstructionMnemonics
  imports "HOL-Word.Word_Bitwise"
begin

datatype instr_mnemonic_8088 =
    Adc | Add | And | Call | Cbw | Clc | Cmc | Cmp | Cwd | Dec | Div |
    Hlt | Inc | Imul |
    Ja | Jae | Jb | Jbe | Jc | Je | Jg | Jge | Jl | Jle | Jna | 
    Jnae | Jnb | Jnbe | Jnc | Jne | Jng | Jnge | Jnl | Jnle | Jno | 
    Jnp | Jns | Jnz | Jo | Jp | Jpe | Jpo | Js | Jz | Jmp | 
    Lea | Mov | Neg | Nop | Not | Or | Pop | Push | Rcl | Ret  |
    Rol | Ror | Sal | Sar | Sbb | Shl | Shr | Stc | Sub | Test | Xchg | Xor
(* Full 8086/8088
datatype instr_mnemonic_8088 =
    Aaa | Aad | Aam | Aas | Adc | Add | And | Call | Cbw | Clc | 
    Cld | Cli | Cmc | Cmp | Cmpsb | Cwd | Daa | Das | Dec | Div | 
    Esc | Hlt | Idiv | Imul | In | Inc | Ins_Int | Into | Iret | Ja | 
    Jae | Jb | Jbe | Jc | Je | Jg | Jge | Jl | Jle | Jna | 
    Jnae | Jnb | Jnbe | Jnc | Jne | Jng | Jnge | Jnl | Jnle | Jno | 
    Jnp | Jns | Jnz | Jo | Jp | Jpe | Jpo | Js | Jz | Jmp | 
    Lahf | Lds | Lea | Les | Lock | Lodsb | Lodsw | Loop | Loope | Loopne | 
    Loopnz | Loopz | Mov | Movsb | Movsw | Mul | Neg | Nop | Not | Or |
    Out | Pop | Popf | Push | Pushf | Rcl | Rcr | Ret | Retn | Retf | 
    Rol | Ror | Sahf | Sal | Sar | Sbb | Scasb | Scasw | Shl | Shr | 
    Stc | Std | Sti | Stosb | Stosw | Sub | Test | Wait | Xchg | Xlat | 
    Xor
Additionally there was (REP, REPE, REPNE, REPNZ, REPZ) (MOVS/STOS/CMPS/LODS/SCAS) introduced 
*)

datatype instr_mnemonic_8088_x87 = Nop8088_x87
(* Full 8086 X87 instructions supported via coprocessor and eventually supported natively 80486 and on.
datatype instr_mnemonic_8088_x87 =
F2xm1 | Fabs  | Fadd  | Faddp  | Fbld  | Fbstp  | Fchs  | Fclex  | Fcom  | Fcomp  | Fcompp  | 
Decstp  | Fdisi  | Fdiv  | Fdivp  | Fdivr  | Fdivrp  | Feni  | Ffree  | Fiadd  | Ficom  |
Ficomp  | Fidiv  | Fidivr  | Fild  | Fimul  | Fincstp  | Finit  | Fist  | Fistp  | Fisub  | 
Isubr  | Fld  | Fld1  | Fldcw  | Fldenv  | Fldenvw  | Fldl2e  | Fldl2t  | Fldlg2  | Fldln2  | 
Ldpi  | Fldz  | Fmul  | Fmulp  | Fnclex  | Fndisi  | Fneni  | Fninit  | Fnop  | Fnsave  | Fnsavew  |
Fnstcw  | Fnstenv  | Fnstenvw  | Fnstsw  | Fpatan  | Fprem  | Fptan  | Frndint  | Frstor  | Frstorw  | 
Save  | Fsavew  | Fscale  | Fsqrt  | Fst  | Fstcw  | Fstenv  | Fstenvw  | Fstp  | Fstsw  | Fsub  |
Fsubp  | Fsubr  | Fsubrp  | Ftst  | Fwait  | Fxam  | Fxch  | Fxtract  | Fyl2x  | Fyl2xp1  
*)

datatype instr_mnemonic_80188 = Leave
(* Full 80186/80188
datatype instr_mnemonic_80188 =
  Bound | Enter | Ins | Leave | Outs | Popa | Pusha 
*)

datatype instr_mnemonic_80286 = Nop80286
(* Full 80286
datatype instr_mnemonic_80286 =
  Arpl | Clts | Lar | Lgdt | Lidt | Lldt | Lmsw | Loadall | Lsl | Ltr | Sgdt | Sidt | Sldt | Smsw
  | Str | Verr | Verw
*)

datatype instr_mnemonic_80286_x87 = Nop80286_x87
(* Full 80286_x87
datatype instr_mnemonic_80286_x87 = Fsetpm
*)

datatype instr_mnemonic_80386 =
  Bsr | Bt | Cdq | Cwde | Movsx | Movzx |
  Seta |  Setae |  Setb |  Setbe |  Setc |  Sete |  Setg |  Setge |  Setl |  Setle |  Setna |  Setnae |  Setnb |  Setnbe |  
  Setnc |  Setne |  Setng |  Setnge |  Setnl |  Setnle |  Setno |  Setnp |  Setns |  Setnz |  Seto |  Setp |  Setpe |  Setpo |  
  Sets |  Setz
(* Full 80386
datatype instr_mnemonic_80386 =
  Bsf | Bsr | Bt | Btc | Btr | Bts | Cdq |  Cwde | Ibts | Insd | Iretd | Iretf | Jecxz | Lfs | 
  Lgs | Lss | Lodsd | Loopw | Loopzw | Loopew | Loopnzw | Loopnew | Loopd | Loopzd | Looped | 
  Loopnzd | Loopned |  Movsx | Movzx | Outsd | Popad | Popfd | Pushad | Pushfd | Scasd | 
  Seta |  Setae |  Setb |  Setbe |  Setc |  Sete |  Setg |  Setge |  Setl |  Setle |  Setna |  Setnae |  Setnb |  Setnbe |  
  Setnc |  Setne |  Setng |  Setnge |  Setnl |  Setnle |  Setno |  Setnp |  Setns |  Setnz |  Seto |  Setp |  Setpe |  Setpo |  
  Sets |  Setz

(* These two are not the same as in SSE2. These are related to strings..  *)
Movsd | Cmpsd | 
*)

datatype instr_mnemonic_80386_x87 = Nop80386_x87
(* Full 80386_x87
datatype instr_mnemonic_80386_x87 =
  Fcos | Fldenvd | Fsaved | Fstenvd | Fprem1 | Frstord | Fsin | Fsincos | Fucom | Fucomp
  Fucompp
*)

datatype instr_mnemonic_80486 =
  Bswap | Cmpxchg | Xadd
(* Full 80486
datatype instr_mnemonic_80486 =
  instr_mnemonic_80386 | 
  Bswap | Cmpxchg | Invd | Invlpg | Wbinvd | Xadd
*)

datatype instr_mnemonic_pentium = NopPentium
(* Full Pentium
datatype instr_mnemonic_pentium =
  Cpuid | Cmpxchg8b | Rdmsr | Rdtsc | Wrmsr | Rsm
*)

datatype instr_mnemonic_pentiummmx = NopPentiumMMX
(* Full Pentium MMX Base Instructions
datatype instr_mnemonic_pentiummmx =
  Rdpmc
*)

datatype instr_mnemonic_pentiummmx_mmx =
  Movd | Movq | Paddd | Paddq | Pand | Pandn | Por | Pxor | Psubd |
  Punpckhwd | Punpckhdq |  Punpcklwd | Punpckldq

(* Full Pentium MMX MMX Instructions
datatype instr_mnemonic_pentiummmx_mmx =
  Emms | Movd | Movq | Packssdw | Packsswb | Packuswb | Paddb | Paddw | Paddd | Paddq | Paddsb | 
  Paddsw | Paddusb | Paddusw | Pand | Pandn | Por | Pxor | Pcmpeqb | Pcmpeqw | Pcmpeqd | Pcmpgtb | 
  Pcmpgtw | Pcmpgtd | Pmaddwd | Pmulhw | Pmullw | Psllw | Pslld | Psllq | Psrad | Psraw | Psrlw | 
  Psrld | Psrlq | Psubb | Psubw | Psubd | Psubsb | Psubsw | Psubusb | Psubusw | Punpckhbw | 
  Punpckhwd | Punpckhdq | Punpcklbw | Punpcklwd | Punpckldq
*)


datatype instr_mnemonic_pentiumpro =
  Cmova |  Cmovae |  Cmovb |  Cmovbe |  Cmovc |  Cmove |  Cmovg |  Cmovge |  Cmovl |  Cmovle | 
  Cmovna |  Cmovnae |  Cmovnb |  Cmovnbe |  Cmovnc |  Cmovne |  Cmovng |  Cmovnge |  Cmovnl |  
  Cmovnle |  Cmovno |  Cmovnp |  Cmovns |  Cmovnz |  Cmovo |  Cmovp |  Cmovpe |  Cmovpo |  Cmovs |  
  Cmovz

(* Full Pentium Pro
datatype instr_mnemonic_pentiumpro =
  Cmova |  Cmovae |  Cmovb |  Cmovbe |  Cmovc |  Cmove |  Cmovg |  Cmovge |  Cmovl |  Cmovle | 
  Cmovna |  Cmovnae |  Cmovnb |  Cmovnbe |  Cmovnc |  Cmovne |  Cmovng |  Cmovnge |  Cmovnl |  
  Cmovnle |  Cmovno |  Cmovnp |  Cmovns |  Cmovnz |  Cmovo |  Cmovp |  Cmovpe |  Cmovpo |  Cmovs |  
  Cmovz | Ud2
*)

datatype instr_mnemonic_pentiumpro_x87 = NopPentPro_x87

(* Full Pentium Pro x87 Instructions
datatype instr_mnemonic_pentiumpro_x87 =
  Fcmovb | Fcmovbe | Fcmove | Fcmovnb | Fcmovnbe | Fcmovne | Fcmovnu | Fcmovu | Fcomi | Fcomip | 
  Fucomi | Fucomip
*)

datatype instr_mnemonic_pentiumii = NopPentiumII
(* Full Pentium
datatype instr_mnemonic_pentiumii =
  Sysenter | Sysexit
*)

datatype instr_mnemonic_sse = NopSSE
(* Full SSE Base Instructions 
datatype instr_mnemonic_sse =
  Maskmovq | Movntq | Prefetcht0 | Prefetcht1 | Prefetcht2 | Prefetchnta | Sfence
*)
datatype instr_mnemonic_sse_x87 = NopSSE_x87
(* Full SSE x87 Instructions
datatype instr_mnemonic_sse_x87 =
  Fxrstor | Fxsave 
*)
datatype instr_mnemonic_sse_simdmmx = Nopsse_simdmmx
(* Full SSE MMX Instructions
datatype instr_mnemonic_sse_simdmmx =
  Pshufw | Pinsrw | Pextrw | Pmovmskb | Pminub | Pmaxub | Pavgb | Pavgw | Pmulhuw | Pminsw | Pmaxsw |
  Psadbw 
*)
datatype instr_mnemonic_sse_simd = 
  Andps | Andnps | Orps | Xorps | Movups | Movss | Movhlps | Unpcklps | Unpckhps | Movlhps | 
  Movaps | Movmskps | Cvtsi2ss | Cvttss2si | Cvtss2si  | Sqrtps | Sqrtss | Rsqrtps | Rsqrtss | Rcpps | Rcpss | Addps | Addss | Mulps | Mulss |
  Subps | Subss | Minps | Minss | Divps | Divss | Maxps | Maxss
(* Full SSE SIMD Instructions
datatype instr_mnemonic_sse_simd =
  Andps | Andnps | Orps | Xorps | Movups | Movss | Movhlps | Movlps | Unpcklps | Unpckhps | Movlhps | 
  Movhps  | Movaps | Movmskps | Cvtpi2ps | Cvtsi2ss | Movntps | Cvttps2pi  | Cvttss2si  | Cvtps2pi | Cvtss2si  | Ucomiss | 
  Comiss | Sqrtps | Sqrtss | Rsqrtps | Rsqrtss | Rcpps | Rcpss | Addps | Addss | Mulps | Mulss |
  Subps | Subss | Minps | Minss | Divps | Divss | Maxps | Maxss | Ldmxcsr | Stmxcsr | Cmpps | Cmpss | 
  Shufps
*)

datatype instr_mnemonic_sse2 = NopSSE2
(* Full SSE2 Base Instructions
datatype instr_mnemonic_sse2 =
  Clflush | Lfence | Mfence | Movnti | Pause
*)
datatype instr_mnemonic_sse2_simdmmx = Psubq
(* Full SSE MMX Instructions
datatype instr_mnemonic_sse2_simdmmx =
  Psubq | Pmuludq 
*)
datatype instr_mnemonic_sse2_simd = 
 Movapd |  Movupd | Movmskpd | Movsd | Addpd | Addsd | Divpd | Divsd | 
 Maxpd | Maxsd | Minpd | Minsd | Mulpd | Mulsd | Sqrtpd | Sqrtsd | Subpd | Subsd | Andpd | Andnpd | 
 Orpd | Xorpd | Ucomisd | Unpckhpd | Unpcklpd | Cvtdq2pd | Cvtdq2ps | 
 Cvtpd2dq | Cvtpd2ps | Cvtps2dq | Cvtps2pd | Cvtsd2si | Cvtsd2ss | Cvtsi2sd | 
 Cvtss2sd | Cvttpd2dq | Cvttps2dq | Cvttsd2si |
 Movdqa | Movdqu | Punpckhqdq | Punpcklqdq 
(* Full SSE2 SIMD Instructions
datatype instr_mnemonic_sse2_simd =
 Movapd | Movntpd | Movhpd | Movlpd | Movupd | Movmskpd | Movsd | Addpd | Addsd | Divpd | Divsd | 
 Maxpd | Maxsd | Minpd | Minsd | Mulpd | Mulsd | Sqrtpd | Sqrtsd | Subpd | Subsd | Andpd | Andnpd | 
 Orpd | Xorpd | Cmppd | Cmpsd | Comisd | Ucomisd | Shufpd | Unpckhpd | Unpcklpd | Cvtdq2pd | Cvtdq2ps | 
 Cvtpd2dq | Cvtpd2pi | Cvtpd2ps | Cvtpi2pd | Cvtps2dq | Cvtps2pd | Cvtsd2si | Cvtsd2ss | Cvtsi2sd | 
 Cvtss2sd | Cvttpd2dq | Cvttpd2pi | Cvttps2dq | Cvttsd2si |  Maskmovdqu | Movdq2q | 
 Movdqa | Movdqu | Movq2dq | Movntdq | Pshufhw | Pshuflw | Pshufd | Pslldq | Psrldq | Punpckhqdq | Punpcklqdq 
*)

datatype instr_mnemonic_x86_64 = 
  Cdqe | Cqo | Movsxd 
(* Full x86_64 Instructions
datatype instr_mnemonic_x86_64 =
  Cdqe | Cqo | Cmpsq | Cmpxchg16b | Iretq | Jrcxz | Lodsq | Movsxd | Popfq | Pushfq | Rdtscp | Scasq | Stosq | Swapgs 
*)

datatype instr_mnemonic_sse3 = NopSSE3
(* Full SSE3 Base Instructions
datatype instr_mnemonic_sse3 =
  Monitor | Mwait 
*)
datatype instr_mnemonic_sse3_x87 = NopSSE3_x87
(* Full SSE3 x87 Instructions
datatype instr_mnemonic_sse3_x87 =
  Fisttp
*)
datatype instr_mnemonic_sse3_simd = 
  Addsubps | Addsubpd | Movddup | Movsldup | Movshdup | Haddps | Haddpd | Hsubps | Hsubpd
(* Full SSE3 SIMD Instructions
datatype instr_mnemonic_sse3_simd =
  Addsubps | Addsubpd | Movddup | Movsldup | Movshdup | Haddps | Haddpd | Hsubps | Hsubpd | Lddqu 
*)


datatype instr_mnemonic_ssse3_simdmmx = 
  Phsubd | Phaddd
(* Full SSSE3 MMX Instructions
datatype instr_mnemonic_ssse3_simdmmx =
  Psignb | Psignw | Psignd | Pshufb | Pmulhrsw | Pmaddubsw | Phsubw | Phsubsw | Phsubd | Phaddsw | Phaddw | Phaddd | Palignr | Pabsb | Pabsw | Pabsd 
*)

datatype instr_mnemonic_sse41_simd = 
  Pmovsxbd | Pmovzxbd | Pmovsxbq | Pmovzxbq | Pmovsxwd | Pmovzxwd | Pmovsxwq | 
  Pmovzxwq | Pmovsxdq | Pmovzxdq 

(* Full SSE4.1 SIMD Instructions
datatype instr_mnemonic_sse41_simd =
  Dpps | Dppd | Blendps | Blendvps | Blendpd | Blendvpd | Roundps | Roundss | Roundpd | Roundsd | 
  Insertps | Extractps | Mpsadbw | Phminposuw | Pmulld | Pmuldq | Pblendvb | Pblendw | Pminsb | Pminuw | Pminsd | Pminud | 
  Pmaxsb | Pmaxuw | Pmaxsd | Pmaxud | Pinsrb | Pinsrd | Pinsrq | Pextrb | Pextrd | Pextrq | 
  Pmovsxbw | Pmovzxbw | Pmovsxbd | Pmovzxbd | Pmovsxbq | Pmovzxbq | Pmovsxwd | Pmovzxwd | Pmovsxwq | 
  Pmovzxwq | Pmovsxdq | Pmovzxdq | Ptest | Pcmpeqq | Packusdw | Movntdqa 
*)

datatype instr_mnemonic_vtx = NopVTX
(* Full VT-x Instructions (Initial set of 10 mnemonics)
datatype instr_mnemonic_vtx =
  Vmptrld | Vmptrst | Vmclear | Vmread | Vmwrite | Vmcall | Vmlaunch | Vmresume | Vmxoff | Vmxon |
  Vmfunc | Invvpid | Invept
*)



datatype instr_mnemonic_sse42 = Popcnt
(* Full SSE3 Base Instructions
datatype instr_mnemonic_sse42 =
  Crc32 | Popcnt
*)
datatype instr_mnemonic_sse42_simd = NopSESE42_SIMD
(* Full SSE4.2 SIMD Instructions
datatype instr_mnemonic_sse42_simd =
  Pcmpestri | Pcmpestrm | Pcmpistri | Pcmpistrm | Pcmpgtq 
*)    
 
datatype instr_mnemonic_avx_group1 = 
  Vsqrtps | Vsqrtpd | Vrsqrtps | Vrcpps | Vaddps | Vaddpd | Vsubps | Vsubpd | Vmulps | Vmulpd | 
  Vdivps | Vdivpd | Vcvtps2pd | Vcvtpd2ps | Vcvtdq2ps | Vcvtps2dq | Vcvttps2dq | Vcvttpd2dq | 
  Vcvtpd2dq | Vcvtdq2pd | Vminps | Vminpd | Vmaxps | Vmaxpd | Vhaddpd | Vhaddps | Vhsubpd | Vhsubps |
  Vaddsubpd | Vaddsubps | Vmovaps | Vmovapd | Vmovdqa | Vmovups | Vmovupd | Vmovdqu | Vmovmskps | Vmovmskpd |
  Vmovshdup | Vmovsldup | Vmovddup | Vunpckhpd | Vunpckhps | Vunpcklpd | Vunpcklps | 
  Vxorps | Vxorpd | Vorps | Vorpd | Vandnpd | Vandnps | Vandpd | Vandps |
Vbroadcastsd | Vbroadcastss | Vzeroall | Vcvtsi2ss | Vcvtsi2sd | Vcvtsd2si | Vcvttss2si | Vcvttsd2si | Vcvtss2si | Vrsqrtss |
  Vrcpss | Vaddss | Vaddsd | Vsubss | Vsubsd | Vmulss | Vmulsd | Vdivss | Vdivsd | Vsqrtss | Vsqrtsd | 
  Vcvtss2sd | Vcvtsd2ss | Vminss | Vminsd | Vmaxss | Vmaxsd | Vpand | Vpandn | Vpor | Vpxor 

datatype instr_mnemonic_avx_group2 =
  Vpaddd | Vpaddq | Vpsubd | Vpsubq | Vphsubd | Vphaddd | Vpmovsxbd | Vpmovzxbd | Vpmovsxbq | 
  Vpmovzxbq | Vpmovsxwd | Vpmovzxwd | Vpmovsxwq | Vpmovzxwq | Vpmovsxdq | Vpmovzxdq |
  Vmovss | Vmovsd | Vmovlhps | Vmovhlps | 
  Vmovq | Vmovd | Vpunpckhwd | Vpunpcklwd | Vpunpckhdq | Vpunpckldq | Vpunpcklqdq | Vpunpckhqdq 

(* Full AVX Instructions 
datatype instr_mnemonic_avx =
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
  Vpavgw | Vpmuludq | Vpcmpeqb | Vpcmpeqw | Vpcmpeqd | Vpmullw | Vpmulhuw | Vpmulhw | Vpsubsw |

  Vpaddsw | Vpsadbw | Vpaddusb | Vpaddusw | Vpaddsb | Vpsubusb | Vpsubusw | Vpsubsb | Vpminub |
  Vpminsw | Vpmaxub | Vpmaxsw | Vpaddb | Vpaddw | Vpaddd | Vpaddq | Vpsubb | Vpsubw | Vpsubd | Vpsubq | 
  Vpsllw | Vpslld | Vpsllq | Vpsraw | Vpsrlw | Vpsrld | Vpsrlq | Vpsrad | Vphsubw | Vphsubd | Vphsubsw | 
  Vphaddw | Vphaddd | Vphaddsw | Vpmulhrsw | Vpsignb | Vpsignw | Vpsignd | Vpabsb | Vpabsw | Vpabsd |
  Vdppd | Vphminposuw | Vmpsadbw | Vpmaxsb | Vpmaxsd | Vpmaxud | Vpminsb | Vpminsd | Vpminud | Vpmaxuw |
  Vpminuw | Vpmovsxbw | Vpmovzxbw | Vpmovsxbd | Vpmovzxbd | Vpmovsxbq | Vpmovzxbq | Vpmovsxwd | Vpmovzxwd | Vpmovsxwq | 
  Vpmovzxwq | Vpmovsxdq | Vpmovzxdq | Vpmuldq | Vpmulld | Vroundsd | Vroundss | Vpopcnt | Vpcmpgtq |
  Vpcmpestri | Vpcmpestrm | Vpcmpistri | Vpcmpistrm | Vpclmulqdq | Vaesdec | Vaesdeclast | Vaesenc |
  Vaesenclast | Vaesimx | Vaeskeygenassist | Vstmxcsr | Vmovss | Vmovsd | Vcmpss | Vcmpsd | Vmovhps | Vmovhpd | Vmovlps | Vmovlpd | 
  Vmovlhps | Vmovhlps | Vmovq | Vmovd | Vpackuswb | Vpackssdw | Vpacksswb | Vpunpckhbw | Vpunpckhwd | 
  Vpunpcklbw | Vpunpcklwd | Vpunpckhdq | Vpunpckldq | Vpunpcklqdq | Vpunpckhqdq | Vpshufhw | Vpshuflw | 
  Vpshufd | Vpmovmskb | Vmaskmovdqu | Vpinsrw | Vpextrw | Vpalignr | 
  Vpshufb | Vextractps | Vinsertps | Vpackusdw | Vpcmpeqq | Vpblendvb | Vpblendw | Vpextrb | 
  Vpextrd | Vpextrq | Vpinsrb | Vpinsrd | Vpinsrq 
*)


 
datatype instr_mnemonic_avx2 = NopAVX2
(* Full AVX2 Instructions --- No new mnemonics were added. Only additional VEX variants for 256-bit 
support on what was already promoted from SSE to 128bit.
datatype instr_mnemonic_avx2 = NopAVX2
*)

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

(* Full FMA SIMD Instructions
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
*)


datatype instr_mnemonic_bm1_bm2 = 
  Andn | Blsi | Blsmsk | Blsr |   Sarx | Shlx | Shrx | Tzcnt

(* Full FMA SIMD Instructions
datatype instr_mnemonic_bm1_bm2 =
  Andn | Bextr | Blsi | Blsmsk | Blsr | Bzhi | Lzcnt | Mulx | Pdep | Pext | Rorx | Sarx | Shlx | Shrx | Tzcnt
*)

(* A couple of random AVX-512 Instructions we Support *)
datatype instr_mnemonic_avx512_f_cd = NopAVX512_F_CD 
datatype instr_mnemonic_avx512_vl_dq_bw =
  Vpbroadcastb | Vpbroadcastd | Vpbroadcastq | Vpbroadcastw 



(* Choosing Instruction Set Based on desired ISA *) 
(*
datatype instr_mnemonic_set_8088 =
        IS_8088     instr_mnemonic_8088

datatype instr_mnemonic_set_8088_w_x87 =
        IS_8088     instr_mnemonic_8088 | 
        IS_8088_x87 instr_mnemonic_8088_x87

datatype instr_mnemonic_set_80188  =
        IS_8088     instr_mnemonic_8088 | 
        IS_80188    instr_mnemonic_80188

datatype instr_mnemonic_set_80188_w_x87 =
        IS_8088     instr_mnemonic_8088 | 
        IS_8088_x87 instr_mnemonic_8088_x87 | 
        IS_80188    instr_mnemonic_80188

datatype instr_mnemonic_set_80286 =
        IS_8088     instr_mnemonic_8088 | 
        IS_80188    instr_mnemonic_80188 | 
        IS_80286    instr_mnemonic_80286 

datatype instr_mnemonic_set_80286_w_x87 =
        IS_8088       instr_mnemonic_8088 | 
        IS_8088_x87   instr_mnemonic_8088_x87 | 
        IS_80188      instr_mnemonic_80188 |
        IS_80286      instr_mnemonic_80286 |
        IS_80286_x87  instr_mnemonic_80286_x87 

datatype instr_mnemonic_set_80386 =
        IS_8088     instr_mnemonic_8088 | 
        IS_80188    instr_mnemonic_80188 | 
        IS_80286    instr_mnemonic_80286 |
        IS_80386    instr_mnemonic_80386 

datatype instr_mnemonic_set_80386_w_x87 =
        IS_8088       instr_mnemonic_8088 | 
        IS_8088_x87   instr_mnemonic_8088_x87 | 
        IS_80188      instr_mnemonic_80188 |
        IS_80286      instr_mnemonic_80286 |
        IS_80286_x87  instr_mnemonic_80286_x87 |
        IS_80386      instr_mnemonic_80386 |
        IS_80386_x87  instr_mnemonic_80386_x87 

datatype instr_mnemonic_set_80486 =
        IS_8088       instr_mnemonic_8088 | 
        IS_8088_x87   instr_mnemonic_8088_x87 | 
        IS_80188      instr_mnemonic_80188 |
        IS_80286      instr_mnemonic_80286 |
        IS_80286_x87  instr_mnemonic_80286_x87 |
        IS_80386      instr_mnemonic_80386 |
        IS_80386_x87  instr_mnemonic_80386_x87 |
        IS_80486      instr_mnemonic_80486

datatype instr_mnemonic_set_pentium =
        IS_8088       instr_mnemonic_8088 | 
        IS_8088_x87   instr_mnemonic_8088_x87 | 
        IS_80188      instr_mnemonic_80188 |
        IS_80286      instr_mnemonic_80286 |
        IS_80286_x87  instr_mnemonic_80286_x87 |
        IS_80386      instr_mnemonic_80386 |
        IS_80386_x87  instr_mnemonic_80386_x87 |
        IS_80486      instr_mnemonic_80486 |
        IS_Pentium    instr_mnemonic_pentium

datatype instr_mnemonic_set_pentiummmx =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx 

datatype instr_mnemonic_set_pentiumpro =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 

datatype instr_mnemonic_set_pentiumii =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii

datatype instr_mnemonic_set_pentiumiii =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd

datatype instr_mnemonic_set_netburst =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd 

datatype instr_mnemonic_set_prescott =
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2             instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64

datatype instr_mnemonic_set_core=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx 

datatype instr_mnemonic_set_penryn=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      instr_mnemonic_sse41_simd | 
        IS_VT_X             instr_mnemonic_vtx

datatype instr_mnemonic_set_nehalem=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      instr_mnemonic_sse41_simd | 
        IS_VT_X             instr_mnemonic_vtx | 
        IS_SSE4_2            instr_mnemonic_sse42 |
        IS_SSE4_2_SIMD      instr_mnemonic_sse42_simd 

datatype instr_mnemonic_set_sandybridge=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      instr_mnemonic_sse41_simd | 
        IS_VT_X             instr_mnemonic_vtx | 
        IS_SSE4_2            instr_mnemonic_sse42 |
        IS_SSE4_2_SIMD      instr_mnemonic_sse42_simd |
        IS_AVX              instr_mnemonic_avx_group1 |
        IS_AVX_2            instr_mnemonic_avx_group2 |

datatype instr_mnemonic_set_haswell=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 |
        IS_80286_x87        instr_mnemonic_80286_x87 |
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 |
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 |
        IS_PentiumII        instr_mnemonic_pentiumii |
        IS_SSE              instr_mnemonic_sse |
        IS_SSE_x87          instr_mnemonic_sse_x87 |
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 |
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 |
        IS_SSE3_x87         instr_mnemonic_sse3_x87 |
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      instr_mnemonic_sse41_simd | 
        IS_VT_X             instr_mnemonic_vtx | 
        IS_SSE4_2            instr_mnemonic_sse42 |
        IS_SSE4_2_SIMD      instr_mnemonic_sse42_simd |
        IS_AVX              instr_mnemonic_avx_group1 |
        IS_AVX_2            instr_mnemonic_avx_group2 |
        IS_AVX2             instr_mnemonic_avx2 |
        IS_FMA              instr_mnemonic_fma |
        IS_BM1_BM2          instr_mnemonic_bm1_bm2
*)
datatype instr_mnemonic_set_skylake_sp=
        IS_8088             instr_mnemonic_8088 | 
        IS_8088_x87         instr_mnemonic_8088_x87 | 
        IS_80188            instr_mnemonic_80188 |
        IS_80286            instr_mnemonic_80286 | 
        IS_80286_x87        instr_mnemonic_80286_x87 | 
        IS_80386            instr_mnemonic_80386 |
        IS_80386_x87        instr_mnemonic_80386_x87 | 
        IS_80486            instr_mnemonic_80486 |
        IS_Pentium          instr_mnemonic_pentium | 
        IS_PentiumMMX       instr_mnemonic_pentiummmx | 
        IS_PentiumMMX_MMX   instr_mnemonic_pentiummmx_mmx | 
        IS_PentiumPro       instr_mnemonic_pentiumpro | 
        IS_PentiumPro_x87   instr_mnemonic_pentiumpro_x87 | 
        IS_PentiumII        instr_mnemonic_pentiumii | 
        IS_SSE              instr_mnemonic_sse | 
        IS_SSE_x87          instr_mnemonic_sse_x87 | 
        IS_SSE_SIMDMMX      instr_mnemonic_sse_simdmmx | 
        IS_SSE_SIMD         instr_mnemonic_sse_simd |
        IS_SSE2              instr_mnemonic_sse2 | 
        IS_SSE2_SIMDMMX     instr_mnemonic_sse2_simdmmx | 
        IS_SSE2_SIMD        instr_mnemonic_sse2_simd |
        IS_SSE3             instr_mnemonic_sse3 | 
        IS_SSE3_x87         instr_mnemonic_sse3_x87 | 
        IS_SSE3_SIMD        instr_mnemonic_sse3_simd |
        IS_X86_64           instr_mnemonic_x86_64 |
        IS_SSSE3_SIMDMMX    instr_mnemonic_ssse3_simdmmx | 
        IS_SSE4_1_SIMD      instr_mnemonic_sse41_simd | 
        IS_VT_X             instr_mnemonic_vtx | 
        IS_SSE4_2            instr_mnemonic_sse42 |
        IS_SSE4_2_SIMD      instr_mnemonic_sse42_simd | 
        IS_AVX              instr_mnemonic_avx_group1 |
        IS_AVX_2            instr_mnemonic_avx_group2 |
        IS_AVX2             instr_mnemonic_avx2 | 
        IS_FMA              instr_mnemonic_fma |
        IS_BM1_BM2          instr_mnemonic_bm1_bm2 | 
        IS_AVX_512_F_CD     instr_mnemonic_avx512_f_cd | 
        IS_AVX_512_VL_DQ_BW instr_mnemonic_avx512_vl_dq_bw  

end
