	.file	"e_remainder.c"
	.intel_syntax noprefix
	.section	.rodata
	.align 8
	.type	zero, @object
	.size	zero, 8
zero:
	.zero	8
	.text
	.globl	__ieee754_remainder
	.type	__ieee754_remainder, @function
__ieee754_remainder:
.LFB0:
	.cfi_startproc
	push	rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	mov	rbp, rsp
	.cfi_def_cfa_register 6
	sub	rsp, 64
	movsd	QWORD PTR -40[rbp], xmm0
	movsd	QWORD PTR -48[rbp], xmm1
	lea	rax, -40[rbp]
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -28[rbp], eax
	lea	rax, -40[rbp]
	add	rax, 4
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -24[rbp], eax
	lea	rax, -48[rbp]
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -20[rbp], eax
	lea	rax, -48[rbp]
	add	rax, 4
	mov	eax, DWORD PTR [rax]
	mov	DWORD PTR -16[rbp], eax
	mov	eax, DWORD PTR -28[rbp]
	and	eax, -2147483648
	mov	DWORD PTR -12[rbp], eax
	and	DWORD PTR -20[rbp], 2147483647
	and	DWORD PTR -28[rbp], 2147483647
	mov	eax, DWORD PTR -20[rbp]
	or	eax, DWORD PTR -16[rbp]
	test	eax, eax
	jne	.L2
	movsd	xmm1, QWORD PTR -40[rbp]
	movsd	xmm0, QWORD PTR -48[rbp]
	mulsd	xmm0, xmm1
	movsd	xmm2, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	mulsd	xmm1, xmm2
	divsd	xmm0, xmm1
	jmp	.L3
.L2:
	cmp	DWORD PTR -28[rbp], 2146435071
	jg	.L4
	cmp	DWORD PTR -20[rbp], 2146435071
	jle	.L5
	mov	eax, DWORD PTR -20[rbp]
	sub	eax, 2146435072
	or	eax, DWORD PTR -16[rbp]
	test	eax, eax
	je	.L5
.L4:
	movsd	xmm1, QWORD PTR -40[rbp]
	movsd	xmm0, QWORD PTR -48[rbp]
	mulsd	xmm0, xmm1
	movsd	xmm2, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	mulsd	xmm1, xmm2
	divsd	xmm0, xmm1
	jmp	.L3
.L5:
	cmp	DWORD PTR -20[rbp], 2145386495
	jg	.L6
	movsd	xmm0, QWORD PTR -48[rbp]
	addsd	xmm0, xmm0
	mov	rax, QWORD PTR -40[rbp]
	movapd	xmm1, xmm0
	mov	QWORD PTR -56[rbp], rax
	movsd	xmm0, QWORD PTR -56[rbp]
	call	__ieee754_fmod@PLT
	movq	rax, xmm0
	mov	QWORD PTR -40[rbp], rax
.L6:
	mov	eax, DWORD PTR -28[rbp]
	sub	eax, DWORD PTR -20[rbp]
	mov	edx, eax
	mov	eax, DWORD PTR -24[rbp]
	sub	eax, DWORD PTR -16[rbp]
	or	eax, edx
	test	eax, eax
	jne	.L7
	pxor	xmm1, xmm1
	movsd	xmm0, QWORD PTR -40[rbp]
	mulsd	xmm0, xmm1
	jmp	.L3
.L7:
	movsd	xmm1, QWORD PTR -40[rbp]
	movq	xmm0, QWORD PTR .LC1[rip]
	andpd	xmm0, xmm1
	movsd	QWORD PTR -40[rbp], xmm0
	movsd	xmm1, QWORD PTR -48[rbp]
	movq	xmm0, QWORD PTR .LC1[rip]
	andpd	xmm0, xmm1
	movsd	QWORD PTR -48[rbp], xmm0
	cmp	DWORD PTR -20[rbp], 2097151
	jg	.L8
	movsd	xmm0, QWORD PTR -40[rbp]
	addsd	xmm0, xmm0
	movsd	xmm1, QWORD PTR -48[rbp]
	ucomisd	xmm0, xmm1
	jbe	.L12
	movsd	xmm0, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	subsd	xmm0, xmm1
	movsd	QWORD PTR -40[rbp], xmm0
	movsd	xmm0, QWORD PTR -40[rbp]
	addsd	xmm0, xmm0
	movsd	xmm1, QWORD PTR -48[rbp]
	ucomisd	xmm0, xmm1
	jb	.L12
	movsd	xmm0, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	subsd	xmm0, xmm1
	movsd	QWORD PTR -40[rbp], xmm0
	jmp	.L12
.L8:
	movsd	xmm1, QWORD PTR -48[rbp]
	movsd	xmm0, QWORD PTR .LC2[rip]
	mulsd	xmm0, xmm1
	movsd	QWORD PTR -8[rbp], xmm0
	movsd	xmm0, QWORD PTR -40[rbp]
	ucomisd	xmm0, QWORD PTR -8[rbp]
	jbe	.L12
	movsd	xmm0, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	subsd	xmm0, xmm1
	movsd	QWORD PTR -40[rbp], xmm0
	movsd	xmm0, QWORD PTR -40[rbp]
	ucomisd	xmm0, QWORD PTR -8[rbp]
	jb	.L12
	movsd	xmm0, QWORD PTR -40[rbp]
	movsd	xmm1, QWORD PTR -48[rbp]
	subsd	xmm0, xmm1
	movsd	QWORD PTR -40[rbp], xmm0
.L12:
	lea	rax, -40[rbp]
	mov	eax, DWORD PTR [rax]
	xor	eax, DWORD PTR -12[rbp]
	mov	edx, eax
	lea	rax, -40[rbp]
	mov	DWORD PTR [rax], edx
	movsd	xmm0, QWORD PTR -40[rbp]
.L3:
	leave
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	__ieee754_remainder, .-__ieee754_remainder
	.section	.rodata
	.align 16
.LC1:
	.long	4294967295
	.long	2147483647
	.long	0
	.long	0
	.align 8
.LC2:
	.long	0
	.long	1071644672
	.ident	"GCC: (Ubuntu 7.2.0-8ubuntu3.2) 7.2.0"
	.section	.note.GNU-stack,"",@progbits
