Inductive instr_mnemonic_8088 : Set :=
    Adc | Add | And | Call | Cbw | Clc | Cmc | Cmp | Cwd | Dec | Div |
    Hlt | Inc | Imul |
    Ja | Jae | Jb | Jbe | Jc | Je | Jg | Jge | Jl | Jle | Jna | 
    Jnae | Jnb | Jnbe | Jnc | Jne | Jng | Jnge | Jnl | Jnle | Jno | 
    Jnp | Jns | Jnz | Jo | Jp | Jpe | Jpo | Js | Jz | Jmp | 
    Lea | Mov | Neg | Nop | Not | Or | Pop | Push | Rcl | Ret  |
    Rol | Ror | Sal | Sar | Sbb | Shl | Shr | Stc | Sub | Test | Xchg | Xor.

Inductive instr_mnemonic_8088_x87 : Set := Nop8088_x87.

Inductive instr_mnemonic_80188 : Set := Leave.

Inductive instr_mnemonic_80286 : Set := Nop80286.

Inductive instr_mnemonic_80286_x87 : Set := Nop80286_x87.

Inductive instr_mnemonic_80386 : Set :=
  Bsr | Bt | Cdq | Cwde | Movsx | Movzx |
  Seta |  Setae |  Setb |  Setbe |  Setc |  Sete |  Setg |  Setge |  Setl |  Setle |  Setna |  Setnae |  Setnb |  Setnbe |  
  Setnc |  Setne |  Setng |  Setnge |  Setnl |  Setnle |  Setno |  Setnp |  Setns |  Setnz |  Seto |  Setp |  Setpe |  Setpo |  
  Sets |  Setz.

Inductive instr_mnemonic_80386_x87 : Set := Nop80386_x87.

Inductive instr_mnemonic_80486 : Set :=
  Bswap | Cmpxchg | Xadd.

Inductive instr_mnemonic_pentium : Set := NopPentium.

Inductive instr_mnemonic_pentiummmx : Set := NopPentiumMMX.

Inductive instr_mnemonic_pentiummmx_mmx : Set :=
  Movd | Movq | Paddd | Paddq | Pand | Pandn | Por | Pxor | Psubd |
  Punpckhwd | Punpckhdq |  Punpcklwd | Punpckldq.

Inductive instr_mnemonic_pentiumpro : Set :=
  Cmova |  Cmovae |  Cmovb |  Cmovbe |  Cmovc |  Cmove |  Cmovg |  Cmovge |  Cmovl |  Cmovle | 
  Cmovna |  Cmovnae |  Cmovnb |  Cmovnbe |  Cmovnc |  Cmovne |  Cmovng |  Cmovnge |  Cmovnl |  
  Cmovnle |  Cmovno |  Cmovnp |  Cmovns |  Cmovnz |  Cmovo |  Cmovp |  Cmovpe |  Cmovpo |  Cmovs |  
  Cmovz.

Inductive instr_mnemonic_pentiumpro_x87 : Set := NopPentPro_x87.

Inductive instr_mnemonic_pentiumii : Set := NopPentiumII.

Inductive instr_mnemonic_sse : Set := NopSSE.

Inductive instr_mnemonic_sse_x87 : Set := NopSSE_x87.

Inductive instr_mnemonic_sse_simdmmx : Set := Nopsse_simdmmx.

Inductive instr_mnemonic_sse_simd := 
  Andps | Andnps | Orps | Xorps | Movups | Movss | Movhlps | Unpcklps | Unpckhps | Movlhps | 
  Movaps | Movmskps | Cvtsi2ss | Cvttss2si | Cvtss2si  | Sqrtps | Sqrtss | Rsqrtps | Rsqrtss | Rcpps | Rcpss | Addps | Addss | Mulps | Mulss |
  Subps | Subss | Minps | Minss | Divps | Divss | Maxps | Maxss.

Inductive instr_mnemonic_sse2 := NopSSE2.

Inductive instr_mnemonic_sse2_simdmmx := Psubq.

Inductive instr_mnemonic_sse2_simd := 
 Movapd |  Movupd | Movmskpd | Movsd | Addpd | Addsd | Divpd | Divsd | 
 Maxpd | Maxsd | Minpd | Minsd | Mulpd | Mulsd | Sqrtpd | Sqrtsd | Subpd | Subsd | Andpd | Andnpd | 
 Orpd | Xorpd | Ucomisd | Unpckhpd | Unpcklpd | Cvtdq2pd | Cvtdq2ps | 
 Cvtpd2dq | Cvtpd2ps | Cvtps2dq | Cvtps2pd | Cvtsd2si | Cvtsd2ss | Cvtsi2sd | 
 Cvtss2sd | Cvttpd2dq | Cvttps2dq | Cvttsd2si |
 Movdqa | Movdqu | Punpckhqdq | Punpcklqdq .

Inductive instr_mnemonic_x86_64 := 
  Cdqe | Cqo | Movsxd .

Inductive instr_mnemonic_sse3 := NopSSE3.

Inductive instr_mnemonic_sse3_x87 := NopSSE3_x87.

Inductive instr_mnemonic_sse3_simd := 
  Addsubps | Addsubpd | Movddup | Movsldup | Movshdup | Haddps | Haddpd | Hsubps | Hsubpd.

Inductive instr_mnemonic_ssse3_simdmmx := 
  Phsubd | Phaddd.

Inductive instr_mnemonic_sse41_simd := 
  Pmovsxbd | Pmovzxbd | Pmovsxbq | Pmovzxbq | Pmovsxwd | Pmovzxwd | Pmovsxwq | 
  Pmovzxwq | Pmovsxdq | Pmovzxdq .

Inductive instr_mnemonic_vtx := NopVTX.

Inductive instr_mnemonic_sse42 := Popcnt.

Inductive instr_mnemonic_sse42_simd := NopSESE42_SIMD.

Inductive instr_mnemonic_avx_group1 := 
  Vsqrtps | Vsqrtpd | Vrsqrtps | Vrcpps | Vaddps | Vaddpd | Vsubps | Vsubpd | Vmulps | Vmulpd | 
  Vdivps | Vdivpd | Vcvtps2pd | Vcvtpd2ps | Vcvtdq2ps | Vcvtps2dq | Vcvttps2dq | Vcvttpd2dq | 
  Vcvtpd2dq | Vcvtdq2pd | Vminps | Vminpd | Vmaxps | Vmaxpd | Vhaddpd | Vhaddps | Vhsubpd | Vhsubps |
  Vaddsubpd | Vaddsubps | Vmovaps | Vmovapd | Vmovdqa | Vmovups | Vmovupd | Vmovdqu | Vmovmskps | Vmovmskpd |
  Vmovshdup | Vmovsldup | Vmovddup | Vunpckhpd | Vunpckhps | Vunpcklpd | Vunpcklps | 
  Vxorps | Vxorpd | Vorps | Vorpd | Vandnpd | Vandnps | Vandpd | Vandps |
Vbroadcastsd | Vbroadcastss | Vzeroall | Vcvtsi2ss | Vcvtsi2sd | Vcvtsd2si | Vcvttss2si | Vcvttsd2si | Vcvtss2si | Vrsqrtss |
  Vrcpss | Vaddss | Vaddsd | Vsubss | Vsubsd | Vmulss | Vmulsd | Vdivss | Vdivsd | Vsqrtss | Vsqrtsd | 
  Vcvtss2sd | Vcvtsd2ss | Vminss | Vminsd | Vmaxss | Vmaxsd | Vpand | Vpandn | Vpor | Vpxor .

Inductive instr_mnemonic_avx_group2 :=
  Vpaddd | Vpaddq | Vpsubd | Vpsubq | Vphsubd | Vphaddd | Vpmovsxbd | Vpmovzxbd | Vpmovsxbq | 
  Vpmovzxbq | Vpmovsxwd | Vpmovzxwd | Vpmovsxwq | Vpmovzxwq | Vpmovsxdq | Vpmovzxdq |
  Vmovss | Vmovsd | Vmovlhps | Vmovhlps | 
  Vmovq | Vmovd | Vpunpckhwd | Vpunpcklwd | Vpunpckhdq | Vpunpckldq | Vpunpcklqdq | Vpunpckhqdq .

Inductive instr_mnemonic_avx2 := NopAVX2.

Inductive instr_mnemonic_fma := 
  Vfmadd132pd | Vfmadd213pd | Vfmadd231pd | Vfmadd132ps | Vfmadd213ps | Vfmadd231ps | Vfmadd132sd | 
Vfmadd213sd | Vfmadd231sd | Vfmadd132ss | Vfmadd213ss | Vfmadd231ss | Vfmaddsub132pd | Vfmaddsub213pd | 
Vfmaddsub231pd | Vfmaddsub132ps | Vfmaddsub213ps | Vfmaddsub231ps | Vfmsubadd132pd | Vfmsubadd213pd | 
Vfmsubadd231pd | Vfmsubadd132ps | Vfmsubadd213ps | Vfmsubadd231ps | Vfmsub132pd | Vfmsub213pd | 
Vfmsub231pd | Vfmsub132ps | Vfmsub213ps | Vfmsub231ps | Vfmsub132sd | Vfmsub213sd | Vfmsub231sd | 
Vfmsub132ss | Vfmsub213ss | Vfmsub231ss | Vfnmadd132pd | Vfnmadd213pd | Vfnmadd231pd | Vfnmadd132ps | 
Vfnmadd213ps | Vfnmadd231ps | Vfnmadd132sd | Vfnmadd213sd | Vfnmadd231sd | Vfnmadd132ss | Vfnmadd213ss | 
Vfnmadd231ss | Vfnmsub132pd | Vfnmsub213pd | Vfnmsub231pd | Vfnmsub132ps | Vfnmsub213ps | Vfnmsub231ps | 
Vfnmsub132sd | Vfnmsub213sd | Vfnmsub231sd | Vfnmsub132ss | Vfnmsub213ss | Vfnmsub231ss .

Inductive instr_mnemonic_bm1_bm2 := 
  Andn | Blsi | Blsmsk | Blsr |   Sarx | Shlx | Shrx | Tzcnt.

Inductive instr_mnemonic_avx512_f_cd := NopAVX512_F_CD.

Inductive instr_mnemonic_avx512_vl_dq_bw :=
  Vpbroadcastb | Vpbroadcastd | Vpbroadcastq | Vpbroadcastw.

Inductive instr_mnemonic_set_skylake_sp :=
| IS_8088 : instr_mnemonic_8088 -> instr_mnemonic_set_skylake_sp
| IS_8088_x87 : instr_mnemonic_8088_x87 -> instr_mnemonic_set_skylake_sp
| IS_80188 : instr_mnemonic_80188 -> instr_mnemonic_set_skylake_sp
| IS_80286 : instr_mnemonic_80286 -> instr_mnemonic_set_skylake_sp
| IS_80286_x87 : instr_mnemonic_80286_x87 -> instr_mnemonic_set_skylake_sp
| IS_80386 : instr_mnemonic_80386 -> instr_mnemonic_set_skylake_sp
| IS_80386_x87 : instr_mnemonic_80386_x87 -> instr_mnemonic_set_skylake_sp
| IS_80486 : instr_mnemonic_80486 -> instr_mnemonic_set_skylake_sp
| IS_Pentium : instr_mnemonic_pentium -> instr_mnemonic_set_skylake_sp
| IS_PentiumMMX : instr_mnemonic_pentiummmx -> instr_mnemonic_set_skylake_sp
| IS_PentiumMMX_MMX : instr_mnemonic_pentiummmx_mmx -> instr_mnemonic_set_skylake_sp
| IS_PentiumPro : instr_mnemonic_pentiumpro -> instr_mnemonic_set_skylake_sp
| IS_PentiumPro_x87 : instr_mnemonic_pentiumpro_x87 -> instr_mnemonic_set_skylake_sp
| IS_PentiumII : instr_mnemonic_pentiumii -> instr_mnemonic_set_skylake_sp
| IS_SSE : instr_mnemonic_sse -> instr_mnemonic_set_skylake_sp
| IS_SSE_x87 : instr_mnemonic_sse_x87 -> instr_mnemonic_set_skylake_sp
| IS_SSE_SIMDMMX : instr_mnemonic_sse_simdmmx -> instr_mnemonic_set_skylake_sp
| IS_SSE_SIMD : instr_mnemonic_sse_simd -> instr_mnemonic_set_skylake_sp
| IS_SSE2 : instr_mnemonic_sse2 -> instr_mnemonic_set_skylake_sp
| IS_SSE2_SIMDMMX : instr_mnemonic_sse2_simdmmx -> instr_mnemonic_set_skylake_sp
| IS_SSE2_SIMD : instr_mnemonic_sse2_simd -> instr_mnemonic_set_skylake_sp
| IS_SSE3 : instr_mnemonic_sse3 -> instr_mnemonic_set_skylake_sp
| IS_SSE3_x87 : instr_mnemonic_sse3_x87 -> instr_mnemonic_set_skylake_sp
| IS_SSE3_SIMD : instr_mnemonic_sse3_simd -> instr_mnemonic_set_skylake_sp
| IS_X86_64 : instr_mnemonic_x86_64 -> instr_mnemonic_set_skylake_sp
| IS_SSSE3_SIMDMMX : instr_mnemonic_ssse3_simdmmx -> instr_mnemonic_set_skylake_sp
| IS_SSE4_1_SIMD : instr_mnemonic_sse41_simd -> instr_mnemonic_set_skylake_sp
| IS_VT_X : instr_mnemonic_vtx -> instr_mnemonic_set_skylake_sp
| IS_SSE4_2 : instr_mnemonic_sse42 -> instr_mnemonic_set_skylake_sp
| IS_SSE4_2_SIMD : instr_mnemonic_sse42_simd -> instr_mnemonic_set_skylake_sp
| IS_AVX : instr_mnemonic_avx_group1 -> instr_mnemonic_set_skylake_sp
| IS_AVX_2 : instr_mnemonic_avx_group2 -> instr_mnemonic_set_skylake_sp
| IS_AVX2 : instr_mnemonic_avx2 -> instr_mnemonic_set_skylake_sp
| IS_FMA : instr_mnemonic_fma -> instr_mnemonic_set_skylake_sp
| IS_BM1_BM2 : instr_mnemonic_bm1_bm2 -> instr_mnemonic_set_skylake_sp
| IS_AVX_512_F_CD : instr_mnemonic_avx512_f_cd -> instr_mnemonic_set_skylake_sp
| IS_AVX_512_VL_DQ_BW : instr_mnemonic_avx512_vl_dq_bw -> instr_mnemonic_set_skylake_sp.
