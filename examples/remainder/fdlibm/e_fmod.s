	.file	"e_fmod.c"
	.intel_syntax noprefix
	.section	.rodata
	.align 8
	.type	one, @object
	.size	one, 8
one:
	.long	0
	.long	1072693248
	.align 16
	.type	Zero, @object
	.size	Zero, 16
Zero:
	.long	0
	.long	0
	.long	0
	.long	-2147483648
	.text
	.globl	__ieee754_fmod
	.type	__ieee754_fmod, @function
__ieee754_fmod:
.LFB0:
	.cfi_startproc
	push	rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	mov	rbp, rsp
	.cfi_def_cfa_register 6
	movsd	QWORD PTR -56[rbp], xmm0
	movsd	QWORD PTR -64[rbp], xmm1
	lea	rax, -56[rbp]
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -40[rbp], eax
	lea	rax, -56[rbp]
	add	rax, 4
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -16[rbp], eax
	lea	rax, -64[rbp]
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -36[rbp], eax
	lea	rax, -64[rbp]
	add	rax, 4
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -12[rbp], eax
	mov	eax, DWORD PTR -40[rbp]
	and	eax, -2147483648
	mov	DWORD PTR -8[rbp], eax
	mov	eax, DWORD PTR -8[rbp]
	xor	DWORD PTR -40[rbp], eax
	and	DWORD PTR -36[rbp], 2147483647
	mov	eax, DWORD PTR -36[rbp]
	or	eax, DWORD PTR -12[rbp]
	test	eax, eax
	je	.L2
	cmp	DWORD PTR -40[rbp], 2146435071
	jg	.L2
	mov	eax, DWORD PTR -12[rbp]
	neg	eax
	or	eax, DWORD PTR -12[rbp]
	shr	eax, 31
	mov	edx, eax
	mov	eax, DWORD PTR -36[rbp]
	or	eax, edx
	cmp	eax, 2146435072
	jbe	.L3
.L2:
	movsd	xmm1, QWORD PTR -56[rbp]
	movsd	xmm0, QWORD PTR -64[rbp]
	mulsd	xmm0, xmm1
	movsd	xmm2, QWORD PTR -56[rbp]
	movsd	xmm1, QWORD PTR -64[rbp]
	mulsd	xmm1, xmm2
	divsd	xmm0, xmm1
	jmp	.L4
.L3:
	mov	eax, DWORD PTR -40[rbp]
	cmp	eax, DWORD PTR -36[rbp]
	jg	.L5
	mov	eax, DWORD PTR -40[rbp]
	cmp	eax, DWORD PTR -36[rbp]
	jl	.L6
	mov	eax, DWORD PTR -16[rbp]
	cmp	eax, DWORD PTR -12[rbp]
	jnb	.L7
.L6:
	movsd	xmm0, QWORD PTR -56[rbp]
	jmp	.L4
.L7:
	mov	eax, DWORD PTR -16[rbp]
	cmp	eax, DWORD PTR -12[rbp]
	jne	.L5
	mov	eax, DWORD PTR -8[rbp]
	shr	eax, 31
	mov	eax, eax
	lea	rdx, 0[0+rax*8]
	lea	rax, Zero[rip]
	movsd	xmm0, QWORD PTR [rdx+rax]
	jmp	.L4
.L5:
	cmp	DWORD PTR -40[rbp], 1048575
	jg	.L8
	cmp	DWORD PTR -40[rbp], 0
	jne	.L9
	mov	DWORD PTR -28[rbp], -1043
	mov	eax, DWORD PTR -16[rbp]
	mov	DWORD PTR -20[rbp], eax
	jmp	.L10
.L11:
	sub	DWORD PTR -28[rbp], 1
	sal	DWORD PTR -20[rbp]
.L10:
	cmp	DWORD PTR -20[rbp], 0
	jg	.L11
	jmp	.L12
.L9:
	mov	DWORD PTR -28[rbp], -1022
	mov	eax, DWORD PTR -40[rbp]
	sal	eax, 11
	mov	DWORD PTR -20[rbp], eax
	jmp	.L13
.L14:
	sub	DWORD PTR -28[rbp], 1
	sal	DWORD PTR -20[rbp]
.L13:
	cmp	DWORD PTR -20[rbp], 0
	jg	.L14
	jmp	.L12
.L8:
	mov	eax, DWORD PTR -40[rbp]
	sar	eax, 20
	sub	eax, 1023
	mov	DWORD PTR -28[rbp], eax
.L12:
	cmp	DWORD PTR -36[rbp], 1048575
	jg	.L15
	cmp	DWORD PTR -36[rbp], 0
	jne	.L16
	mov	DWORD PTR -24[rbp], -1043
	mov	eax, DWORD PTR -12[rbp]
	mov	DWORD PTR -20[rbp], eax
	jmp	.L17
.L18:
	sub	DWORD PTR -24[rbp], 1
	sal	DWORD PTR -20[rbp]
.L17:
	cmp	DWORD PTR -20[rbp], 0
	jg	.L18
	jmp	.L19
.L16:
	mov	DWORD PTR -24[rbp], -1022
	mov	eax, DWORD PTR -36[rbp]
	sal	eax, 11
	mov	DWORD PTR -20[rbp], eax
	jmp	.L20
.L21:
	sub	DWORD PTR -24[rbp], 1
	sal	DWORD PTR -20[rbp]
.L20:
	cmp	DWORD PTR -20[rbp], 0
	jg	.L21
	jmp	.L19
.L15:
	mov	eax, DWORD PTR -36[rbp]
	sar	eax, 20
	sub	eax, 1023
	mov	DWORD PTR -24[rbp], eax
.L19:
	cmp	DWORD PTR -28[rbp], -1022
	jl	.L22
	mov	eax, DWORD PTR -40[rbp]
	and	eax, 1048575
	or	eax, 1048576
	mov	DWORD PTR -40[rbp], eax
	jmp	.L23
.L22:
	mov	eax, -1022
	sub	eax, DWORD PTR -28[rbp]
	mov	DWORD PTR -44[rbp], eax
	cmp	DWORD PTR -44[rbp], 31
	jg	.L24
	mov	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -40[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	mov	esi, eax
	mov	eax, 32
	sub	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -16[rbp]
	mov	ecx, eax
	shr	edx, cl
	mov	eax, edx
	or	eax, esi
	mov	DWORD PTR -40[rbp], eax
	mov	eax, DWORD PTR -44[rbp]
	mov	ecx, eax
	sal	DWORD PTR -16[rbp], cl
	jmp	.L23
.L24:
	mov	eax, DWORD PTR -44[rbp]
	sub	eax, 32
	mov	edx, DWORD PTR -16[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	mov	DWORD PTR -40[rbp], eax
	mov	DWORD PTR -16[rbp], 0
.L23:
	cmp	DWORD PTR -24[rbp], -1022
	jl	.L25
	mov	eax, DWORD PTR -36[rbp]
	and	eax, 1048575
	or	eax, 1048576
	mov	DWORD PTR -36[rbp], eax
	jmp	.L26
.L25:
	mov	eax, -1022
	sub	eax, DWORD PTR -24[rbp]
	mov	DWORD PTR -44[rbp], eax
	cmp	DWORD PTR -44[rbp], 31
	jg	.L27
	mov	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -36[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	mov	esi, eax
	mov	eax, 32
	sub	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -12[rbp]
	mov	ecx, eax
	shr	edx, cl
	mov	eax, edx
	or	eax, esi
	mov	DWORD PTR -36[rbp], eax
	mov	eax, DWORD PTR -44[rbp]
	mov	ecx, eax
	sal	DWORD PTR -12[rbp], cl
	jmp	.L26
.L27:
	mov	eax, DWORD PTR -44[rbp]
	sub	eax, 32
	mov	edx, DWORD PTR -12[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	mov	DWORD PTR -36[rbp], eax
	mov	DWORD PTR -12[rbp], 0
.L26:
	mov	eax, DWORD PTR -28[rbp]
	sub	eax, DWORD PTR -24[rbp]
	mov	DWORD PTR -44[rbp], eax
	jmp	.L28
.L32:
	mov	eax, DWORD PTR -40[rbp]
	sub	eax, DWORD PTR -36[rbp]
	mov	DWORD PTR -32[rbp], eax
	mov	eax, DWORD PTR -16[rbp]
	sub	eax, DWORD PTR -12[rbp]
	mov	DWORD PTR -4[rbp], eax
	mov	eax, DWORD PTR -16[rbp]
	cmp	eax, DWORD PTR -12[rbp]
	jnb	.L29
	sub	DWORD PTR -32[rbp], 1
.L29:
	cmp	DWORD PTR -32[rbp], 0
	jns	.L30
	mov	eax, DWORD PTR -40[rbp]
	add	eax, eax
	mov	edx, eax
	mov	eax, DWORD PTR -16[rbp]
	shr	eax, 31
	add	eax, edx
	mov	DWORD PTR -40[rbp], eax
	sal	DWORD PTR -16[rbp]
	jmp	.L28
.L30:
	mov	eax, DWORD PTR -32[rbp]
	or	eax, DWORD PTR -4[rbp]
	test	eax, eax
	jne	.L31
	mov	eax, DWORD PTR -8[rbp]
	shr	eax, 31
	mov	eax, eax
	lea	rdx, 0[0+rax*8]
	lea	rax, Zero[rip]
	movsd	xmm0, QWORD PTR [rdx+rax]
	jmp	.L4
.L31:
	mov	eax, DWORD PTR -32[rbp]
	add	eax, eax
	mov	edx, eax
	mov	eax, DWORD PTR -4[rbp]
	shr	eax, 31
	add	eax, edx
	mov	DWORD PTR -40[rbp], eax
	mov	eax, DWORD PTR -4[rbp]
	add	eax, eax
	mov	DWORD PTR -16[rbp], eax
.L28:
	mov	eax, DWORD PTR -44[rbp]
	lea	edx, -1[rax]
	mov	DWORD PTR -44[rbp], edx
	test	eax, eax
	jne	.L32
	mov	eax, DWORD PTR -40[rbp]
	sub	eax, DWORD PTR -36[rbp]
	mov	DWORD PTR -32[rbp], eax
	mov	eax, DWORD PTR -16[rbp]
	sub	eax, DWORD PTR -12[rbp]
	mov	DWORD PTR -4[rbp], eax
	mov	eax, DWORD PTR -16[rbp]
	cmp	eax, DWORD PTR -12[rbp]
	jnb	.L33
	sub	DWORD PTR -32[rbp], 1
.L33:
	cmp	DWORD PTR -32[rbp], 0
	js	.L34
	mov	eax, DWORD PTR -32[rbp]
	mov	DWORD PTR -40[rbp], eax
	mov	eax, DWORD PTR -4[rbp]
	mov	DWORD PTR -16[rbp], eax
.L34:
	mov	eax, DWORD PTR -40[rbp]
	or	eax, DWORD PTR -16[rbp]
	test	eax, eax
	jne	.L36
	mov	eax, DWORD PTR -8[rbp]
	shr	eax, 31
	mov	eax, eax
	lea	rdx, 0[0+rax*8]
	lea	rax, Zero[rip]
	movsd	xmm0, QWORD PTR [rdx+rax]
	jmp	.L4
.L37:
	mov	eax, DWORD PTR -40[rbp]
	add	eax, eax
	mov	edx, eax
	mov	eax, DWORD PTR -16[rbp]
	shr	eax, 31
	add	eax, edx
	mov	DWORD PTR -40[rbp], eax
	sal	DWORD PTR -16[rbp]
	sub	DWORD PTR -24[rbp], 1
.L36:
	cmp	DWORD PTR -40[rbp], 1048575
	jle	.L37
	cmp	DWORD PTR -24[rbp], -1022
	jl	.L38
	mov	eax, DWORD PTR -40[rbp]
	lea	edx, -1048576[rax]
	mov	eax, DWORD PTR -24[rbp]
	add	eax, 1023
	sal	eax, 20
	or	eax, edx
	mov	DWORD PTR -40[rbp], eax
	lea	rax, -56[rbp]
	mov	edx, DWORD PTR -40[rbp]
	or	edx, DWORD PTR -8[rbp]
	mov	DWORD PTR [rax], edx
	lea	rax, -56[rbp]
	add	rax, 4
	mov	edx, DWORD PTR -16[rbp]
	mov	DWORD PTR [rax], edx
	jmp	.L39
.L38:
	mov	eax, -1022
	sub	eax, DWORD PTR -24[rbp]
	mov	DWORD PTR -44[rbp], eax
	cmp	DWORD PTR -44[rbp], 20
	jg	.L40
	mov	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -16[rbp]
	mov	esi, edx
	mov	ecx, eax
	shr	esi, cl
	mov	edx, DWORD PTR -40[rbp]
	mov	eax, 32
	sub	eax, DWORD PTR -44[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	or	eax, esi
	mov	DWORD PTR -16[rbp], eax
	mov	eax, DWORD PTR -44[rbp]
	mov	ecx, eax
	sar	DWORD PTR -40[rbp], cl
	jmp	.L41
.L40:
	cmp	DWORD PTR -44[rbp], 31
	jg	.L42
	mov	eax, 32
	sub	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -40[rbp]
	mov	ecx, eax
	sal	edx, cl
	mov	eax, edx
	mov	esi, eax
	mov	eax, DWORD PTR -44[rbp]
	mov	edx, DWORD PTR -16[rbp]
	mov	ecx, eax
	shr	edx, cl
	mov	eax, edx
	or	eax, esi
	mov	DWORD PTR -16[rbp], eax
	mov	eax, DWORD PTR -8[rbp]
	mov	DWORD PTR -40[rbp], eax
	jmp	.L41
.L42:
	mov	eax, DWORD PTR -44[rbp]
	sub	eax, 32
	mov	edx, DWORD PTR -40[rbp]
	mov	ecx, eax
	sar	edx, cl
	mov	eax, edx
	mov	DWORD PTR -16[rbp], eax
	mov	eax, DWORD PTR -8[rbp]
	mov	DWORD PTR -40[rbp], eax
.L41:
	lea	rax, -56[rbp]
	mov	edx, DWORD PTR -40[rbp]
	or	edx, DWORD PTR -8[rbp]
	mov	DWORD PTR [rax], edx
	lea	rax, -56[rbp]
	add	rax, 4
	mov	edx, DWORD PTR -16[rbp]
	mov	DWORD PTR [rax], edx
	movsd	xmm1, QWORD PTR -56[rbp]
	movsd	xmm0, QWORD PTR .LC0[rip]
	mulsd	xmm0, xmm1
	movsd	QWORD PTR -56[rbp], xmm0
.L39:
	movsd	xmm0, QWORD PTR -56[rbp]
.L4:
	pop	rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	__ieee754_fmod, .-__ieee754_fmod
	.section	.rodata
	.align 8
.LC0:
	.long	0
	.long	1072693248
	.ident	"GCC: (Ubuntu 7.2.0-8ubuntu3.2) 7.2.0"
	.section	.note.GNU-stack,"",@progbits
