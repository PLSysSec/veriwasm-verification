	.intel_syntax noprefix

	## Size 1
	# 0x400526:	push	rbp [REG]
	.globl main
	.type main, @function
main:
	push	rbp
	## Size 3
	# 0x400527:	mov	rbp, rsp [REG, REG]
	mov	rbp, rsp
	## Size 4
	# 0x40052a:	sub	rsp, 0x30 [REG, IMM]
	sub	rsp, 0x30
	## Size 10
	# 0x40052e:	movabs	rax, 0x4014000000000000 [REG, IMM]
	movabs	rax, 0x4014000000000000
	## Size 4
	# 0x400538:	mov	qword ptr [rbp - 0x18], rax [MEM, REG]
	mov	qword ptr [rbp - 0x18], rax
	## Size 10
	# 0x40053c:	movabs	rax, 0x3ff199999999999a [REG, IMM]
	movabs	rax, 0x3ff199999999999a
	## Size 4
	# 0x400546:	mov	qword ptr [rbp - 0x10], rax [MEM, REG]
	mov	qword ptr [rbp - 0x10], rax
	## Size 4
	# 0x40054a:	mov	rdx, qword ptr [rbp - 0x10] [REG, MEM]
	mov	rdx, qword ptr [rbp - 0x10]
	## Size 4
	# 0x40054e:	mov	rax, qword ptr [rbp - 0x18] [REG, MEM]
	mov	rax, qword ptr [rbp - 0x18]
	## Size 4
	# 0x400552:	mov	qword ptr [rbp - 0x28], rdx [MEM, REG]
	mov	qword ptr [rbp - 0x28], rdx
	## Size 5
	# 0x400556:	movsd	xmm1, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x28]
	## Size 4
	# 0x40055b:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 5
	# 0x40055f:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400564:	call	0x400a49 [IMM <CODEREF>]
	call	__ieee754_remainder
	## Size 5
	# 0x400569:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x40056e:	mov	qword ptr [rbp - 8], rax [MEM, REG]
	mov	qword ptr [rbp - 8], rax
	## Size 4
	# 0x400572:	mov	rcx, qword ptr [rbp - 8] [REG, MEM]
	mov	rcx, qword ptr [rbp - 8]
	## Size 4
	# 0x400576:	mov	rdx, qword ptr [rbp - 0x10] [REG, MEM]
	mov	rdx, qword ptr [rbp - 0x10]
	## Size 4
	# 0x40057a:	mov	rax, qword ptr [rbp - 0x18] [REG, MEM]
	mov	rax, qword ptr [rbp - 0x18]
	## Size 4
	# 0x40057e:	mov	qword ptr [rbp - 0x28], rcx [MEM, REG]
	mov	qword ptr [rbp - 0x28], rcx
	## Size 5
	# 0x400582:	movsd	xmm2, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm2, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400587:	mov	qword ptr [rbp - 0x28], rdx [MEM, REG]
	mov	qword ptr [rbp - 0x28], rdx
	## Size 5
	# 0x40058b:	movsd	xmm1, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400590:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 5
	# 0x400594:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400599:	mov	edi, 0x400d28 [REG, IMM <DATAREF>]
	mov	edi, OFFSET FLAT:label_9
	## Size 5
	# 0x40059e:	mov	eax, 3 [REG, IMM]
	mov	eax, 3
	## Size 5
	# 0x4005a3:	call	0x400400 [IMM <CODEREF>]
	call	printf
	## Size 5
	# 0x4005a8:	mov	eax, 0 [REG, IMM]
	mov	eax, 0
	## Size 1
	# 0x4005ad:	leave	 []
	leave	
	## Size 1
	# 0x4005ae:	ret	 []
	ret	
	.section	.text
	.align	16
	#Procedure 0x4005af

	## Size 1
	# 0x4005af:	push	rbp [REG]
	.globl __ieee754_fmod
	.type __ieee754_fmod, @function
__ieee754_fmod:
	push	rbp
	## Size 3
	# 0x4005b0:	mov	rbp, rsp [REG, REG]
	mov	rbp, rsp
	## Size 5
	# 0x4005b3:	movsd	qword ptr [rbp - 0x38], xmm0 [MEM, REG]
	movsd	qword ptr [rbp - 0x38], xmm0
	## Size 5
	# 0x4005b8:	movsd	qword ptr [rbp - 0x40], xmm1 [MEM, REG]
	movsd	qword ptr [rbp - 0x40], xmm1
	## Size 4
	# 0x4005bd:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x38]
	## Size 2
	# 0x4005c1:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x4005c3:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 4
	# 0x4005c6:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x38]
	## Size 4
	# 0x4005ca:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 2
	# 0x4005ce:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x4005d0:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 4
	# 0x4005d3:	lea	rax, qword ptr [rbp - 0x40] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x40]
	## Size 2
	# 0x4005d7:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x4005d9:	mov	dword ptr [rbp - 0x24], eax [MEM, REG]
	mov	dword ptr [rbp - 0x24], eax
	## Size 4
	# 0x4005dc:	lea	rax, qword ptr [rbp - 0x40] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x40]
	## Size 4
	# 0x4005e0:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 2
	# 0x4005e4:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x4005e6:	mov	dword ptr [rbp - 0xc], eax [MEM, REG]
	mov	dword ptr [rbp - 0xc], eax
	## Size 3
	# 0x4005e9:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 5
	# 0x4005ec:	and	eax, 0x80000000 [REG, IMM]
	and	eax, 0x80000000
	## Size 3
	# 0x4005f1:	mov	dword ptr [rbp - 8], eax [MEM, REG]
	mov	dword ptr [rbp - 8], eax
	## Size 3
	# 0x4005f4:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x4005f7:	xor	dword ptr [rbp - 0x28], eax [MEM, REG]
	xor	dword ptr [rbp - 0x28], eax
	## Size 7
	# 0x4005fa:	and	dword ptr [rbp - 0x24], 0x7fffffff [MEM, IMM]
	and	dword ptr [rbp - 0x24], 0x7fffffff
	## Size 3
	# 0x400601:	mov	eax, dword ptr [rbp - 0x24] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x24]
	## Size 3
	# 0x400604:	or	eax, dword ptr [rbp - 0xc] [REG, MEM]
	or	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400607:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400609:	je	0x40062d [IMM <CODEREF>]
	je	.label_13
	## Size 7
	# 0x40060b:	cmp	dword ptr [rbp - 0x28], 0x7fefffff [MEM, IMM]
	cmp	dword ptr [rbp - 0x28], 0x7fefffff
	## Size 2
	# 0x400612:	jg	0x40062d [IMM <CODEREF>]
	jg	.label_13
	## Size 3
	# 0x400614:	mov	eax, dword ptr [rbp - 0xc] [REG, MEM]
	mov	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400617:	neg	eax [REG]
	neg	eax
	## Size 3
	# 0x400619:	or	eax, dword ptr [rbp - 0xc] [REG, MEM]
	or	eax, dword ptr [rbp - 0xc]
	## Size 3
	# 0x40061c:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x40061f:	mov	edx, eax [REG, REG]
	mov	edx, eax
	## Size 3
	# 0x400621:	mov	eax, dword ptr [rbp - 0x24] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x24]
	## Size 2
	# 0x400624:	or	eax, edx [REG, REG]
	or	eax, edx
	## Size 5
	# 0x400626:	cmp	eax, 0x7ff00000 [REG, IMM]
	cmp	eax, 0x7ff00000
	## Size 2
	# 0x40062b:	jbe	0x400657 [IMM <CODEREF>]
	jbe	.label_15
	## Size 5
	# 0x40062d:	movsd	xmm1, qword ptr [rbp - 0x38] [REG, MEM]
.label_13:
	movsd	xmm1, qword ptr [rbp - 0x38]
	## Size 5
	# 0x400632:	movsd	xmm0, qword ptr [rbp - 0x40] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x40]
	## Size 4
	# 0x400637:	mulsd	xmm0, xmm1 [REG, REG]
	mulsd	xmm0, xmm1
	## Size 5
	# 0x40063b:	movsd	xmm2, qword ptr [rbp - 0x38] [REG, MEM]
	movsd	xmm2, qword ptr [rbp - 0x38]
	## Size 5
	# 0x400640:	movsd	xmm1, qword ptr [rbp - 0x40] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x40]
	## Size 4
	# 0x400645:	mulsd	xmm1, xmm2 [REG, REG]
	mulsd	xmm1, xmm2
	## Size 4
	# 0x400649:	divsd	xmm0, xmm1 [REG, REG]
	divsd	xmm0, xmm1
	## Size 5
	# 0x40064d:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 5
	# 0x400652:	jmp	0x400a3e [IMM <CODEREF>]
	jmp	.label_10
	## Size 3
	# 0x400657:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
.label_15:
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x40065a:	cmp	eax, dword ptr [rbp - 0x24] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0x24]
	## Size 2
	# 0x40065d:	jg	0x400695 [IMM <CODEREF>]
	jg	.label_38
	## Size 3
	# 0x40065f:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x400662:	cmp	eax, dword ptr [rbp - 0x24] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0x24]
	## Size 2
	# 0x400665:	jl	0x40066f [IMM <CODEREF>]
	jl	.label_42
	## Size 3
	# 0x400667:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x40066a:	cmp	eax, dword ptr [rbp - 0xc] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x40066d:	jae	0x400678 [IMM <CODEREF>]
	jae	.label_45
	## Size 4
	# 0x40066f:	mov	rax, qword ptr [rbp - 0x38] [REG, MEM]
.label_42:
	mov	rax, qword ptr [rbp - 0x38]
	## Size 5
	# 0x400673:	jmp	0x400a3e [IMM <CODEREF>]
	jmp	.label_10
	## Size 3
	# 0x400678:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
.label_45:
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x40067b:	cmp	eax, dword ptr [rbp - 0xc] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x40067e:	jne	0x400695 [IMM <CODEREF>]
	jne	.label_38
	## Size 3
	# 0x400680:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x400683:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x400686:	mov	eax, eax [REG, REG]
	mov	eax, eax
	## Size 8
	# 0x400688:	mov	rax, qword ptr [rax*8 + 0x400d60] [REG, MEM]
	mov	rax,  qword ptr [word ptr [+ (rax * 8) + Zero]]
	## Size 5
	# 0x400690:	jmp	0x400a3e [IMM <CODEREF>]
	jmp	.label_10
	## Size 7
	# 0x400695:	cmp	dword ptr [rbp - 0x28], 0xfffff [MEM, IMM]
.label_38:
	cmp	dword ptr [rbp - 0x28], 0xfffff
	## Size 2
	# 0x40069c:	jg	0x4006e3 [IMM <CODEREF>]
	jg	.label_16
	## Size 4
	# 0x40069e:	cmp	dword ptr [rbp - 0x28], 0 [MEM, IMM]
	cmp	dword ptr [rbp - 0x28], 0
	## Size 2
	# 0x4006a2:	jne	0x4006c2 [IMM <CODEREF>]
	jne	.label_20
	## Size 7
	# 0x4006a4:	mov	dword ptr [rbp - 0x1c], 0xfffffbed [MEM, IMM]
	mov	dword ptr [rbp - 0x1c], 0xfffffbed
	## Size 3
	# 0x4006ab:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x4006ae:	mov	dword ptr [rbp - 0x14], eax [MEM, REG]
	mov	dword ptr [rbp - 0x14], eax
	## Size 2
	# 0x4006b1:	jmp	0x4006ba [IMM <CODEREF>]
	jmp	.label_22
	## Size 4
	# 0x4006b3:	sub	dword ptr [rbp - 0x1c], 1 [MEM, IMM]
.label_25:
	sub	dword ptr [rbp - 0x1c], 1
	## Size 3
	# 0x4006b7:	shl	dword ptr [rbp - 0x14], 1 [MEM, IMM]
	shl	dword ptr [rbp - 0x14], 1
	## Size 4
	# 0x4006ba:	cmp	dword ptr [rbp - 0x14], 0 [MEM, IMM]
.label_22:
	cmp	dword ptr [rbp - 0x14], 0
	## Size 2
	# 0x4006be:	jg	0x4006b3 [IMM <CODEREF>]
	jg	.label_25
	## Size 2
	# 0x4006c0:	jmp	0x4006f1 [IMM <CODEREF>]
	jmp	.label_26
	## Size 7
	# 0x4006c2:	mov	dword ptr [rbp - 0x1c], 0xfffffc02 [MEM, IMM]
.label_20:
	mov	dword ptr [rbp - 0x1c], 0xfffffc02
	## Size 3
	# 0x4006c9:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x4006cc:	shl	eax, 0xb [REG, IMM]
	shl	eax, 0xb
	## Size 3
	# 0x4006cf:	mov	dword ptr [rbp - 0x14], eax [MEM, REG]
	mov	dword ptr [rbp - 0x14], eax
	## Size 2
	# 0x4006d2:	jmp	0x4006db [IMM <CODEREF>]
	jmp	.label_28
	## Size 4
	# 0x4006d4:	sub	dword ptr [rbp - 0x1c], 1 [MEM, IMM]
.label_39:
	sub	dword ptr [rbp - 0x1c], 1
	## Size 3
	# 0x4006d8:	shl	dword ptr [rbp - 0x14], 1 [MEM, IMM]
	shl	dword ptr [rbp - 0x14], 1
	## Size 4
	# 0x4006db:	cmp	dword ptr [rbp - 0x14], 0 [MEM, IMM]
.label_28:
	cmp	dword ptr [rbp - 0x14], 0
	## Size 2
	# 0x4006df:	jg	0x4006d4 [IMM <CODEREF>]
	jg	.label_39
	## Size 2
	# 0x4006e1:	jmp	0x4006f1 [IMM <CODEREF>]
	jmp	.label_26
	## Size 3
	# 0x4006e3:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
.label_16:
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x4006e6:	sar	eax, 0x14 [REG, IMM]
	sar	eax, 0x14
	## Size 5
	# 0x4006e9:	sub	eax, 0x3ff [REG, IMM]
	sub	eax, 0x3ff
	## Size 3
	# 0x4006ee:	mov	dword ptr [rbp - 0x1c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x1c], eax
	## Size 7
	# 0x4006f1:	cmp	dword ptr [rbp - 0x24], 0xfffff [MEM, IMM]
.label_26:
	cmp	dword ptr [rbp - 0x24], 0xfffff
	## Size 2
	# 0x4006f8:	jg	0x40073f [IMM <CODEREF>]
	jg	.label_48
	## Size 4
	# 0x4006fa:	cmp	dword ptr [rbp - 0x24], 0 [MEM, IMM]
	cmp	dword ptr [rbp - 0x24], 0
	## Size 2
	# 0x4006fe:	jne	0x40071e [IMM <CODEREF>]
	jne	.label_50
	## Size 7
	# 0x400700:	mov	dword ptr [rbp - 0x18], 0xfffffbed [MEM, IMM]
	mov	dword ptr [rbp - 0x18], 0xfffffbed
	## Size 3
	# 0x400707:	mov	eax, dword ptr [rbp - 0xc] [REG, MEM]
	mov	eax, dword ptr [rbp - 0xc]
	## Size 3
	# 0x40070a:	mov	dword ptr [rbp - 0x14], eax [MEM, REG]
	mov	dword ptr [rbp - 0x14], eax
	## Size 2
	# 0x40070d:	jmp	0x400716 [IMM <CODEREF>]
	jmp	.label_11
	## Size 4
	# 0x40070f:	sub	dword ptr [rbp - 0x18], 1 [MEM, IMM]
.label_17:
	sub	dword ptr [rbp - 0x18], 1
	## Size 3
	# 0x400713:	shl	dword ptr [rbp - 0x14], 1 [MEM, IMM]
	shl	dword ptr [rbp - 0x14], 1
	## Size 4
	# 0x400716:	cmp	dword ptr [rbp - 0x14], 0 [MEM, IMM]
.label_11:
	cmp	dword ptr [rbp - 0x14], 0
	## Size 2
	# 0x40071a:	jg	0x40070f [IMM <CODEREF>]
	jg	.label_17
	## Size 2
	# 0x40071c:	jmp	0x40074d [IMM <CODEREF>]
	jmp	.label_19
	## Size 7
	# 0x40071e:	mov	dword ptr [rbp - 0x18], 0xfffffc02 [MEM, IMM]
.label_50:
	mov	dword ptr [rbp - 0x18], 0xfffffc02
	## Size 3
	# 0x400725:	mov	eax, dword ptr [rbp - 0x24] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x24]
	## Size 3
	# 0x400728:	shl	eax, 0xb [REG, IMM]
	shl	eax, 0xb
	## Size 3
	# 0x40072b:	mov	dword ptr [rbp - 0x14], eax [MEM, REG]
	mov	dword ptr [rbp - 0x14], eax
	## Size 2
	# 0x40072e:	jmp	0x400737 [IMM <CODEREF>]
	jmp	.label_23
	## Size 4
	# 0x400730:	sub	dword ptr [rbp - 0x18], 1 [MEM, IMM]
.label_24:
	sub	dword ptr [rbp - 0x18], 1
	## Size 3
	# 0x400734:	shl	dword ptr [rbp - 0x14], 1 [MEM, IMM]
	shl	dword ptr [rbp - 0x14], 1
	## Size 4
	# 0x400737:	cmp	dword ptr [rbp - 0x14], 0 [MEM, IMM]
.label_23:
	cmp	dword ptr [rbp - 0x14], 0
	## Size 2
	# 0x40073b:	jg	0x400730 [IMM <CODEREF>]
	jg	.label_24
	## Size 2
	# 0x40073d:	jmp	0x40074d [IMM <CODEREF>]
	jmp	.label_19
	## Size 3
	# 0x40073f:	mov	eax, dword ptr [rbp - 0x24] [REG, MEM]
.label_48:
	mov	eax, dword ptr [rbp - 0x24]
	## Size 3
	# 0x400742:	sar	eax, 0x14 [REG, IMM]
	sar	eax, 0x14
	## Size 5
	# 0x400745:	sub	eax, 0x3ff [REG, IMM]
	sub	eax, 0x3ff
	## Size 3
	# 0x40074a:	mov	dword ptr [rbp - 0x18], eax [MEM, REG]
	mov	dword ptr [rbp - 0x18], eax
	## Size 7
	# 0x40074d:	cmp	dword ptr [rbp - 0x1c], 0xfffffc02 [MEM, IMM]
.label_19:
	cmp	dword ptr [rbp - 0x1c], 0xfffffc02
	## Size 2
	# 0x400754:	jl	0x400768 [IMM <CODEREF>]
	jl	.label_33
	## Size 3
	# 0x400756:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 5
	# 0x400759:	and	eax, 0xfffff [REG, IMM]
	and	eax, 0xfffff
	## Size 5
	# 0x40075e:	or	eax, 0x100000 [REG, IMM]
	or	eax, 0x100000
	## Size 3
	# 0x400763:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 2
	# 0x400766:	jmp	0x4007c0 [IMM <CODEREF>]
	jmp	.label_37
	## Size 5
	# 0x400768:	mov	eax, 0xfffffc02 [REG, IMM]
.label_33:
	mov	eax, 0xfffffc02
	## Size 3
	# 0x40076d:	sub	eax, dword ptr [rbp - 0x1c] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x1c]
	## Size 3
	# 0x400770:	mov	dword ptr [rbp - 0x2c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x2c], eax
	## Size 4
	# 0x400773:	cmp	dword ptr [rbp - 0x2c], 0x1f [MEM, IMM]
	cmp	dword ptr [rbp - 0x2c], 0x1f
	## Size 2
	# 0x400777:	jg	0x4007a7 [IMM <CODEREF>]
	jg	.label_46
	## Size 3
	# 0x400779:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x40077c:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 2
	# 0x40077f:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x400781:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x400783:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x400785:	mov	esi, eax [REG, REG]
	mov	esi, eax
	## Size 5
	# 0x400787:	mov	eax, 0x20 [REG, IMM]
	mov	eax, 0x20
	## Size 3
	# 0x40078c:	sub	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x40078f:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400792:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x400794:	shr	edx, cl [REG, REG]
	shr	edx, cl
	## Size 2
	# 0x400796:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x400798:	or	eax, esi [REG, REG]
	or	eax, esi
	## Size 3
	# 0x40079a:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 3
	# 0x40079d:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 2
	# 0x4007a0:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 3
	# 0x4007a2:	shl	dword ptr [rbp - 0x10], cl [MEM, REG]
	shl	dword ptr [rbp - 0x10], cl
	## Size 2
	# 0x4007a5:	jmp	0x4007c0 [IMM <CODEREF>]
	jmp	.label_37
	## Size 3
	# 0x4007a7:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
.label_46:
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4007aa:	sub	eax, 0x20 [REG, IMM]
	sub	eax, 0x20
	## Size 3
	# 0x4007ad:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x4007b0:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4007b2:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x4007b4:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 3
	# 0x4007b6:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 7
	# 0x4007b9:	mov	dword ptr [rbp - 0x10], 0 [MEM, IMM]
	mov	dword ptr [rbp - 0x10], 0
	## Size 7
	# 0x4007c0:	cmp	dword ptr [rbp - 0x18], 0xfffffc02 [MEM, IMM]
.label_37:
	cmp	dword ptr [rbp - 0x18], 0xfffffc02
	## Size 2
	# 0x4007c7:	jl	0x4007db [IMM <CODEREF>]
	jl	.label_29
	## Size 3
	# 0x4007c9:	mov	eax, dword ptr [rbp - 0x24] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x24]
	## Size 5
	# 0x4007cc:	and	eax, 0xfffff [REG, IMM]
	and	eax, 0xfffff
	## Size 5
	# 0x4007d1:	or	eax, 0x100000 [REG, IMM]
	or	eax, 0x100000
	## Size 3
	# 0x4007d6:	mov	dword ptr [rbp - 0x24], eax [MEM, REG]
	mov	dword ptr [rbp - 0x24], eax
	## Size 2
	# 0x4007d9:	jmp	0x400833 [IMM <CODEREF>]
	jmp	.label_31
	## Size 5
	# 0x4007db:	mov	eax, 0xfffffc02 [REG, IMM]
.label_29:
	mov	eax, 0xfffffc02
	## Size 3
	# 0x4007e0:	sub	eax, dword ptr [rbp - 0x18] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x18]
	## Size 3
	# 0x4007e3:	mov	dword ptr [rbp - 0x2c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x2c], eax
	## Size 4
	# 0x4007e6:	cmp	dword ptr [rbp - 0x2c], 0x1f [MEM, IMM]
	cmp	dword ptr [rbp - 0x2c], 0x1f
	## Size 2
	# 0x4007ea:	jg	0x40081a [IMM <CODEREF>]
	jg	.label_21
	## Size 3
	# 0x4007ec:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4007ef:	mov	edx, dword ptr [rbp - 0x24] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x24]
	## Size 2
	# 0x4007f2:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4007f4:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x4007f6:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x4007f8:	mov	esi, eax [REG, REG]
	mov	esi, eax
	## Size 5
	# 0x4007fa:	mov	eax, 0x20 [REG, IMM]
	mov	eax, 0x20
	## Size 3
	# 0x4007ff:	sub	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x400802:	mov	edx, dword ptr [rbp - 0xc] [REG, MEM]
	mov	edx, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400805:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x400807:	shr	edx, cl [REG, REG]
	shr	edx, cl
	## Size 2
	# 0x400809:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x40080b:	or	eax, esi [REG, REG]
	or	eax, esi
	## Size 3
	# 0x40080d:	mov	dword ptr [rbp - 0x24], eax [MEM, REG]
	mov	dword ptr [rbp - 0x24], eax
	## Size 3
	# 0x400810:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 2
	# 0x400813:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 3
	# 0x400815:	shl	dword ptr [rbp - 0xc], cl [MEM, REG]
	shl	dword ptr [rbp - 0xc], cl
	## Size 2
	# 0x400818:	jmp	0x400833 [IMM <CODEREF>]
	jmp	.label_31
	## Size 3
	# 0x40081a:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
.label_21:
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x40081d:	sub	eax, 0x20 [REG, IMM]
	sub	eax, 0x20
	## Size 3
	# 0x400820:	mov	edx, dword ptr [rbp - 0xc] [REG, MEM]
	mov	edx, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400823:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x400825:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x400827:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 3
	# 0x400829:	mov	dword ptr [rbp - 0x24], eax [MEM, REG]
	mov	dword ptr [rbp - 0x24], eax
	## Size 7
	# 0x40082c:	mov	dword ptr [rbp - 0xc], 0 [MEM, IMM]
	mov	dword ptr [rbp - 0xc], 0
	## Size 3
	# 0x400833:	mov	eax, dword ptr [rbp - 0x1c] [REG, MEM]
.label_31:
	mov	eax, dword ptr [rbp - 0x1c]
	## Size 3
	# 0x400836:	sub	eax, dword ptr [rbp - 0x18] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x18]
	## Size 3
	# 0x400839:	mov	dword ptr [rbp - 0x2c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x2c], eax
	## Size 2
	# 0x40083c:	jmp	0x4008b7 [IMM <CODEREF>]
	jmp	.label_27
	## Size 3
	# 0x40083e:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
.label_32:
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x400841:	sub	eax, dword ptr [rbp - 0x24] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x24]
	## Size 3
	# 0x400844:	mov	dword ptr [rbp - 0x20], eax [MEM, REG]
	mov	dword ptr [rbp - 0x20], eax
	## Size 3
	# 0x400847:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x40084a:	sub	eax, dword ptr [rbp - 0xc] [REG, MEM]
	sub	eax, dword ptr [rbp - 0xc]
	## Size 3
	# 0x40084d:	mov	dword ptr [rbp - 4], eax [MEM, REG]
	mov	dword ptr [rbp - 4], eax
	## Size 3
	# 0x400850:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x400853:	cmp	eax, dword ptr [rbp - 0xc] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400856:	jae	0x40085c [IMM <CODEREF>]
	jae	.label_49
	## Size 4
	# 0x400858:	sub	dword ptr [rbp - 0x20], 1 [MEM, IMM]
	sub	dword ptr [rbp - 0x20], 1
	## Size 4
	# 0x40085c:	cmp	dword ptr [rbp - 0x20], 0 [MEM, IMM]
.label_49:
	cmp	dword ptr [rbp - 0x20], 0
	## Size 2
	# 0x400860:	jns	0x40087e [IMM <CODEREF>]
	jns	.label_40
	## Size 3
	# 0x400862:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 2
	# 0x400865:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 2
	# 0x400867:	mov	edx, eax [REG, REG]
	mov	edx, eax
	## Size 3
	# 0x400869:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x40086c:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x40086f:	add	eax, edx [REG, REG]
	add	eax, edx
	## Size 3
	# 0x400871:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 3
	# 0x400874:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400877:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 3
	# 0x400879:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 2
	# 0x40087c:	jmp	0x4008b7 [IMM <CODEREF>]
	jmp	.label_27
	## Size 3
	# 0x40087e:	mov	eax, dword ptr [rbp - 0x20] [REG, MEM]
.label_40:
	mov	eax, dword ptr [rbp - 0x20]
	## Size 3
	# 0x400881:	or	eax, dword ptr [rbp - 4] [REG, MEM]
	or	eax, dword ptr [rbp - 4]
	## Size 2
	# 0x400884:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400886:	jne	0x40089d [IMM <CODEREF>]
	jne	.label_51
	## Size 3
	# 0x400888:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x40088b:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x40088e:	mov	eax, eax [REG, REG]
	mov	eax, eax
	## Size 8
	# 0x400890:	mov	rax, qword ptr [rax*8 + 0x400d60] [REG, MEM]
	mov	rax,  qword ptr [word ptr [+ (rax * 8) + Zero]]
	## Size 5
	# 0x400898:	jmp	0x400a3e [IMM <CODEREF>]
	jmp	.label_10
	## Size 3
	# 0x40089d:	mov	eax, dword ptr [rbp - 0x20] [REG, MEM]
.label_51:
	mov	eax, dword ptr [rbp - 0x20]
	## Size 2
	# 0x4008a0:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 2
	# 0x4008a2:	mov	edx, eax [REG, REG]
	mov	edx, eax
	## Size 3
	# 0x4008a4:	mov	eax, dword ptr [rbp - 4] [REG, MEM]
	mov	eax, dword ptr [rbp - 4]
	## Size 3
	# 0x4008a7:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x4008aa:	add	eax, edx [REG, REG]
	add	eax, edx
	## Size 3
	# 0x4008ac:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 3
	# 0x4008af:	mov	eax, dword ptr [rbp - 4] [REG, MEM]
	mov	eax, dword ptr [rbp - 4]
	## Size 2
	# 0x4008b2:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 3
	# 0x4008b4:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x4008b7:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
.label_27:
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4008ba:	lea	edx, dword ptr [rax - 1] [REG, MEM]
	lea	edx, dword ptr [rax - 1]
	## Size 3
	# 0x4008bd:	mov	dword ptr [rbp - 0x2c], edx [MEM, REG]
	mov	dword ptr [rbp - 0x2c], edx
	## Size 2
	# 0x4008c0:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 6
	# 0x4008c2:	jne	0x40083e [IMM <CODEREF>]
	jne	.label_32
	## Size 3
	# 0x4008c8:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x4008cb:	sub	eax, dword ptr [rbp - 0x24] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x24]
	## Size 3
	# 0x4008ce:	mov	dword ptr [rbp - 0x20], eax [MEM, REG]
	mov	dword ptr [rbp - 0x20], eax
	## Size 3
	# 0x4008d1:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x4008d4:	sub	eax, dword ptr [rbp - 0xc] [REG, MEM]
	sub	eax, dword ptr [rbp - 0xc]
	## Size 3
	# 0x4008d7:	mov	dword ptr [rbp - 4], eax [MEM, REG]
	mov	dword ptr [rbp - 4], eax
	## Size 3
	# 0x4008da:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x4008dd:	cmp	eax, dword ptr [rbp - 0xc] [REG, MEM]
	cmp	eax, dword ptr [rbp - 0xc]
	## Size 2
	# 0x4008e0:	jae	0x4008e6 [IMM <CODEREF>]
	jae	.label_30
	## Size 4
	# 0x4008e2:	sub	dword ptr [rbp - 0x20], 1 [MEM, IMM]
	sub	dword ptr [rbp - 0x20], 1
	## Size 4
	# 0x4008e6:	cmp	dword ptr [rbp - 0x20], 0 [MEM, IMM]
.label_30:
	cmp	dword ptr [rbp - 0x20], 0
	## Size 2
	# 0x4008ea:	js	0x4008f8 [IMM <CODEREF>]
	js	.label_44
	## Size 3
	# 0x4008ec:	mov	eax, dword ptr [rbp - 0x20] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x20]
	## Size 3
	# 0x4008ef:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 3
	# 0x4008f2:	mov	eax, dword ptr [rbp - 4] [REG, MEM]
	mov	eax, dword ptr [rbp - 4]
	## Size 3
	# 0x4008f5:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x4008f8:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
.label_44:
	mov	eax, dword ptr [rbp - 0x28]
	## Size 3
	# 0x4008fb:	or	eax, dword ptr [rbp - 0x10] [REG, MEM]
	or	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x4008fe:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400900:	jne	0x400917 [IMM <CODEREF>]
	jne	.label_35
	## Size 3
	# 0x400902:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x400905:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x400908:	mov	eax, eax [REG, REG]
	mov	eax, eax
	## Size 8
	# 0x40090a:	mov	rax, qword ptr [rax*8 + 0x400d60] [REG, MEM]
	mov	rax,  qword ptr [word ptr [+ (rax * 8) + Zero]]
	## Size 5
	# 0x400912:	jmp	0x400a3e [IMM <CODEREF>]
	jmp	.label_10
	## Size 2
	# 0x400917:	jmp	0x400937 [IMM <CODEREF>]
.label_35:
	jmp	.label_18
	## Size 3
	# 0x400919:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
.label_47:
	mov	eax, dword ptr [rbp - 0x28]
	## Size 2
	# 0x40091c:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 2
	# 0x40091e:	mov	edx, eax [REG, REG]
	mov	edx, eax
	## Size 3
	# 0x400920:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 3
	# 0x400923:	shr	eax, 0x1f [REG, IMM]
	shr	eax, 0x1f
	## Size 2
	# 0x400926:	add	eax, edx [REG, REG]
	add	eax, edx
	## Size 3
	# 0x400928:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 3
	# 0x40092b:	mov	eax, dword ptr [rbp - 0x10] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x40092e:	add	eax, eax [REG, REG]
	add	eax, eax
	## Size 3
	# 0x400930:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 4
	# 0x400933:	sub	dword ptr [rbp - 0x18], 1 [MEM, IMM]
	sub	dword ptr [rbp - 0x18], 1
	## Size 7
	# 0x400937:	cmp	dword ptr [rbp - 0x28], 0xfffff [MEM, IMM]
.label_18:
	cmp	dword ptr [rbp - 0x28], 0xfffff
	## Size 2
	# 0x40093e:	jle	0x400919 [IMM <CODEREF>]
	jle	.label_47
	## Size 7
	# 0x400940:	cmp	dword ptr [rbp - 0x18], 0xfffffc02 [MEM, IMM]
	cmp	dword ptr [rbp - 0x18], 0xfffffc02
	## Size 2
	# 0x400947:	jl	0x400980 [IMM <CODEREF>]
	jl	.label_34
	## Size 3
	# 0x400949:	mov	eax, dword ptr [rbp - 0x28] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x28]
	## Size 6
	# 0x40094c:	lea	edx, dword ptr [rax - 0x100000] [REG, MEM]
	lea	edx, dword ptr [rax - 0x100000]
	## Size 3
	# 0x400952:	mov	eax, dword ptr [rbp - 0x18] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x18]
	## Size 5
	# 0x400955:	add	eax, 0x3ff [REG, IMM]
	add	eax, 0x3ff
	## Size 3
	# 0x40095a:	shl	eax, 0x14 [REG, IMM]
	shl	eax, 0x14
	## Size 2
	# 0x40095d:	or	eax, edx [REG, REG]
	or	eax, edx
	## Size 3
	# 0x40095f:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 4
	# 0x400962:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x38]
	## Size 3
	# 0x400966:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 3
	# 0x400969:	or	edx, dword ptr [rbp - 8] [REG, MEM]
	or	edx, dword ptr [rbp - 8]
	## Size 2
	# 0x40096c:	mov	dword ptr [rax], edx [MEM, REG]
	mov	dword ptr [rax], edx
	## Size 4
	# 0x40096e:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x38]
	## Size 4
	# 0x400972:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 3
	# 0x400976:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400979:	mov	dword ptr [rax], edx [MEM, REG]
	mov	dword ptr [rax], edx
	## Size 5
	# 0x40097b:	jmp	0x400a3a [IMM <CODEREF>]
	jmp	.label_41
	## Size 5
	# 0x400980:	mov	eax, 0xfffffc02 [REG, IMM]
.label_34:
	mov	eax, 0xfffffc02
	## Size 3
	# 0x400985:	sub	eax, dword ptr [rbp - 0x18] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x18]
	## Size 3
	# 0x400988:	mov	dword ptr [rbp - 0x2c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x2c], eax
	## Size 4
	# 0x40098b:	cmp	dword ptr [rbp - 0x2c], 0x14 [MEM, IMM]
	cmp	dword ptr [rbp - 0x2c], 0x14
	## Size 2
	# 0x40098f:	jg	0x4009bd [IMM <CODEREF>]
	jg	.label_36
	## Size 3
	# 0x400991:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x400994:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400997:	mov	esi, edx [REG, REG]
	mov	esi, edx
	## Size 2
	# 0x400999:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x40099b:	shr	esi, cl [REG, REG]
	shr	esi, cl
	## Size 3
	# 0x40099d:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 5
	# 0x4009a0:	mov	eax, 0x20 [REG, IMM]
	mov	eax, 0x20
	## Size 3
	# 0x4009a5:	sub	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x2c]
	## Size 2
	# 0x4009a8:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4009aa:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x4009ac:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x4009ae:	or	eax, esi [REG, REG]
	or	eax, esi
	## Size 3
	# 0x4009b0:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x4009b3:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 2
	# 0x4009b6:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 3
	# 0x4009b8:	sar	dword ptr [rbp - 0x28], cl [MEM, REG]
	sar	dword ptr [rbp - 0x28], cl
	## Size 2
	# 0x4009bb:	jmp	0x400a07 [IMM <CODEREF>]
	jmp	.label_14
	## Size 4
	# 0x4009bd:	cmp	dword ptr [rbp - 0x2c], 0x1f [MEM, IMM]
.label_36:
	cmp	dword ptr [rbp - 0x2c], 0x1f
	## Size 2
	# 0x4009c1:	jg	0x4009ef [IMM <CODEREF>]
	jg	.label_43
	## Size 5
	# 0x4009c3:	mov	eax, 0x20 [REG, IMM]
	mov	eax, 0x20
	## Size 3
	# 0x4009c8:	sub	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4009cb:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 2
	# 0x4009ce:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4009d0:	shl	edx, cl [REG, REG]
	shl	edx, cl
	## Size 2
	# 0x4009d2:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x4009d4:	mov	esi, eax [REG, REG]
	mov	esi, eax
	## Size 3
	# 0x4009d6:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4009d9:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x4009dc:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4009de:	shr	edx, cl [REG, REG]
	shr	edx, cl
	## Size 2
	# 0x4009e0:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 2
	# 0x4009e2:	or	eax, esi [REG, REG]
	or	eax, esi
	## Size 3
	# 0x4009e4:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x4009e7:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x4009ea:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 2
	# 0x4009ed:	jmp	0x400a07 [IMM <CODEREF>]
	jmp	.label_14
	## Size 3
	# 0x4009ef:	mov	eax, dword ptr [rbp - 0x2c] [REG, MEM]
.label_43:
	mov	eax, dword ptr [rbp - 0x2c]
	## Size 3
	# 0x4009f2:	sub	eax, 0x20 [REG, IMM]
	sub	eax, 0x20
	## Size 3
	# 0x4009f5:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 2
	# 0x4009f8:	mov	ecx, eax [REG, REG]
	mov	ecx, eax
	## Size 2
	# 0x4009fa:	sar	edx, cl [REG, REG]
	sar	edx, cl
	## Size 2
	# 0x4009fc:	mov	eax, edx [REG, REG]
	mov	eax, edx
	## Size 3
	# 0x4009fe:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x400a01:	mov	eax, dword ptr [rbp - 8] [REG, MEM]
	mov	eax, dword ptr [rbp - 8]
	## Size 3
	# 0x400a04:	mov	dword ptr [rbp - 0x28], eax [MEM, REG]
	mov	dword ptr [rbp - 0x28], eax
	## Size 4
	# 0x400a07:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
.label_14:
	lea	rax, qword ptr [rbp - 0x38]
	## Size 3
	# 0x400a0b:	mov	edx, dword ptr [rbp - 0x28] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x28]
	## Size 3
	# 0x400a0e:	or	edx, dword ptr [rbp - 8] [REG, MEM]
	or	edx, dword ptr [rbp - 8]
	## Size 2
	# 0x400a11:	mov	dword ptr [rax], edx [MEM, REG]
	mov	dword ptr [rax], edx
	## Size 4
	# 0x400a13:	lea	rax, qword ptr [rbp - 0x38] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x38]
	## Size 4
	# 0x400a17:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 3
	# 0x400a1b:	mov	edx, dword ptr [rbp - 0x10] [REG, MEM]
	mov	edx, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400a1e:	mov	dword ptr [rax], edx [MEM, REG]
	mov	dword ptr [rax], edx
	## Size 5
	# 0x400a20:	movsd	xmm1, qword ptr [rbp - 0x38] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x38]
	## Size 8
	# 0x400a25:	movsd	xmm0, qword ptr [rip + 0x343] [REG, MEM]
	movsd	xmm0,  qword ptr [word ptr [rip + label_12]]
	## Size 4
	# 0x400a2d:	mulsd	xmm1, xmm0 [REG, REG]
	mulsd	xmm1, xmm0
	## Size 5
	# 0x400a31:	movq	rax, xmm1 [REG, REG]
	movq	rax, xmm1
	## Size 4
	# 0x400a36:	mov	qword ptr [rbp - 0x38], rax [MEM, REG]
	mov	qword ptr [rbp - 0x38], rax
	## Size 4
	# 0x400a3a:	mov	rax, qword ptr [rbp - 0x38] [REG, MEM]
.label_41:
	mov	rax, qword ptr [rbp - 0x38]
	## Size 4
	# 0x400a3e:	mov	qword ptr [rbp - 0x48], rax [MEM, REG]
.label_10:
	mov	qword ptr [rbp - 0x48], rax
	## Size 5
	# 0x400a42:	movsd	xmm0, qword ptr [rbp - 0x48] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x48]
	## Size 1
	# 0x400a47:	pop	rbp [REG]
	pop	rbp
	## Size 1
	# 0x400a48:	ret	 []
	ret	
	.section	.text
	.align	16
	#Procedure 0x400a49

	## Size 1
	# 0x400a49:	push	rbp [REG]
	.globl __ieee754_remainder
	.type __ieee754_remainder, @function
__ieee754_remainder:
	push	rbp
	## Size 3
	# 0x400a4a:	mov	rbp, rsp [REG, REG]
	mov	rbp, rsp
	## Size 4
	# 0x400a4d:	sub	rsp, 0x40 [REG, IMM]
	sub	rsp, 0x40
	## Size 5
	# 0x400a51:	movsd	qword ptr [rbp - 0x28], xmm0 [MEM, REG]
	movsd	qword ptr [rbp - 0x28], xmm0
	## Size 5
	# 0x400a56:	movsd	qword ptr [rbp - 0x30], xmm1 [MEM, REG]
	movsd	qword ptr [rbp - 0x30], xmm1
	## Size 4
	# 0x400a5b:	lea	rax, qword ptr [rbp - 0x28] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x28]
	## Size 2
	# 0x400a5f:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x400a61:	mov	dword ptr [rbp - 0x1c], eax [MEM, REG]
	mov	dword ptr [rbp - 0x1c], eax
	## Size 4
	# 0x400a64:	lea	rax, qword ptr [rbp - 0x28] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400a68:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 2
	# 0x400a6c:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x400a6e:	mov	dword ptr [rbp - 0x18], eax [MEM, REG]
	mov	dword ptr [rbp - 0x18], eax
	## Size 4
	# 0x400a71:	lea	rax, qword ptr [rbp - 0x30] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x30]
	## Size 2
	# 0x400a75:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x400a77:	mov	dword ptr [rbp - 0x14], eax [MEM, REG]
	mov	dword ptr [rbp - 0x14], eax
	## Size 4
	# 0x400a7a:	lea	rax, qword ptr [rbp - 0x30] [REG, MEM]
	lea	rax, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400a7e:	add	rax, 4 [REG, IMM]
	add	rax, 4
	## Size 2
	# 0x400a82:	mov	eax, dword ptr [rax] [REG, MEM]
	mov	eax, dword ptr [rax]
	## Size 3
	# 0x400a84:	mov	dword ptr [rbp - 0x10], eax [MEM, REG]
	mov	dword ptr [rbp - 0x10], eax
	## Size 3
	# 0x400a87:	mov	eax, dword ptr [rbp - 0x1c] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x1c]
	## Size 5
	# 0x400a8a:	and	eax, 0x80000000 [REG, IMM]
	and	eax, 0x80000000
	## Size 3
	# 0x400a8f:	mov	dword ptr [rbp - 0xc], eax [MEM, REG]
	mov	dword ptr [rbp - 0xc], eax
	## Size 7
	# 0x400a92:	and	dword ptr [rbp - 0x14], 0x7fffffff [MEM, IMM]
	and	dword ptr [rbp - 0x14], 0x7fffffff
	## Size 7
	# 0x400a99:	and	dword ptr [rbp - 0x1c], 0x7fffffff [MEM, IMM]
	and	dword ptr [rbp - 0x1c], 0x7fffffff
	## Size 3
	# 0x400aa0:	mov	eax, dword ptr [rbp - 0x14] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x14]
	## Size 3
	# 0x400aa3:	or	eax, dword ptr [rbp - 0x10] [REG, MEM]
	or	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400aa6:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400aa8:	jne	0x400ad4 [IMM <CODEREF>]
	jne	.label_57
	## Size 5
	# 0x400aaa:	movsd	xmm1, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400aaf:	movsd	xmm0, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400ab4:	mulsd	xmm0, xmm1 [REG, REG]
	mulsd	xmm0, xmm1
	## Size 5
	# 0x400ab8:	movsd	xmm2, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm2, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400abd:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400ac2:	mulsd	xmm1, xmm2 [REG, REG]
	mulsd	xmm1, xmm2
	## Size 4
	# 0x400ac6:	divsd	xmm0, xmm1 [REG, REG]
	divsd	xmm0, xmm1
	## Size 5
	# 0x400aca:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 5
	# 0x400acf:	jmp	0x400c8a [IMM <CODEREF>]
	jmp	.label_55
	## Size 7
	# 0x400ad4:	cmp	dword ptr [rbp - 0x1c], 0x7fefffff [MEM, IMM]
.label_57:
	cmp	dword ptr [rbp - 0x1c], 0x7fefffff
	## Size 2
	# 0x400adb:	jg	0x400af5 [IMM <CODEREF>]
	jg	.label_60
	## Size 7
	# 0x400add:	cmp	dword ptr [rbp - 0x14], 0x7fefffff [MEM, IMM]
	cmp	dword ptr [rbp - 0x14], 0x7fefffff
	## Size 2
	# 0x400ae4:	jle	0x400b1f [IMM <CODEREF>]
	jle	.label_61
	## Size 3
	# 0x400ae6:	mov	eax, dword ptr [rbp - 0x14] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x14]
	## Size 5
	# 0x400ae9:	sub	eax, 0x7ff00000 [REG, IMM]
	sub	eax, 0x7ff00000
	## Size 3
	# 0x400aee:	or	eax, dword ptr [rbp - 0x10] [REG, MEM]
	or	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400af1:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400af3:	je	0x400b1f [IMM <CODEREF>]
	je	.label_61
	## Size 5
	# 0x400af5:	movsd	xmm1, qword ptr [rbp - 0x28] [REG, MEM]
.label_60:
	movsd	xmm1, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400afa:	movsd	xmm0, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400aff:	mulsd	xmm0, xmm1 [REG, REG]
	mulsd	xmm0, xmm1
	## Size 5
	# 0x400b03:	movsd	xmm2, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm2, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400b08:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400b0d:	mulsd	xmm1, xmm2 [REG, REG]
	mulsd	xmm1, xmm2
	## Size 4
	# 0x400b11:	divsd	xmm0, xmm1 [REG, REG]
	divsd	xmm0, xmm1
	## Size 5
	# 0x400b15:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 5
	# 0x400b1a:	jmp	0x400c8a [IMM <CODEREF>]
	jmp	.label_55
	## Size 7
	# 0x400b1f:	cmp	dword ptr [rbp - 0x14], 0x7fdfffff [MEM, IMM]
.label_61:
	cmp	dword ptr [rbp - 0x14], 0x7fdfffff
	## Size 2
	# 0x400b26:	jg	0x400b50 [IMM <CODEREF>]
	jg	.label_54
	## Size 5
	# 0x400b28:	movsd	xmm0, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400b2d:	addsd	xmm0, xmm0 [REG, REG]
	addsd	xmm0, xmm0
	## Size 4
	# 0x400b31:	mov	rax, qword ptr [rbp - 0x28] [REG, MEM]
	mov	rax, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400b35:	movapd	xmm1, xmm0 [REG, REG]
	movapd	xmm1, xmm0
	## Size 4
	# 0x400b39:	mov	qword ptr [rbp - 0x38], rax [MEM, REG]
	mov	qword ptr [rbp - 0x38], rax
	## Size 5
	# 0x400b3d:	movsd	xmm0, qword ptr [rbp - 0x38] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x38]
	## Size 5
	# 0x400b42:	call	0x4005af [IMM <CODEREF>]
	call	__ieee754_fmod
	## Size 5
	# 0x400b47:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x400b4c:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 3
	# 0x400b50:	mov	eax, dword ptr [rbp - 0x1c] [REG, MEM]
.label_54:
	mov	eax, dword ptr [rbp - 0x1c]
	## Size 3
	# 0x400b53:	sub	eax, dword ptr [rbp - 0x14] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x14]
	## Size 2
	# 0x400b56:	mov	edx, eax [REG, REG]
	mov	edx, eax
	## Size 3
	# 0x400b58:	mov	eax, dword ptr [rbp - 0x18] [REG, MEM]
	mov	eax, dword ptr [rbp - 0x18]
	## Size 3
	# 0x400b5b:	sub	eax, dword ptr [rbp - 0x10] [REG, MEM]
	sub	eax, dword ptr [rbp - 0x10]
	## Size 2
	# 0x400b5e:	or	eax, edx [REG, REG]
	or	eax, edx
	## Size 2
	# 0x400b60:	test	eax, eax [REG, REG]
	test	eax, eax
	## Size 2
	# 0x400b62:	jne	0x400b7b [IMM <CODEREF>]
	jne	.label_58
	## Size 4
	# 0x400b64:	pxor	xmm1, xmm1 [REG, REG]
	pxor	xmm1, xmm1
	## Size 5
	# 0x400b68:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400b6d:	mulsd	xmm1, xmm0 [REG, REG]
	mulsd	xmm1, xmm0
	## Size 5
	# 0x400b71:	movq	rax, xmm1 [REG, REG]
	movq	rax, xmm1
	## Size 5
	# 0x400b76:	jmp	0x400c8a [IMM <CODEREF>]
	jmp	.label_55
	## Size 5
	# 0x400b7b:	movsd	xmm1, qword ptr [rbp - 0x28] [REG, MEM]
.label_58:
	movsd	xmm1, qword ptr [rbp - 0x28]
	## Size 8
	# 0x400b80:	movsd	xmm0, qword ptr [rip + 0x208] [REG, MEM]
	movsd	xmm0,  qword ptr [word ptr [rip + label_62]]
	## Size 4
	# 0x400b88:	andpd	xmm1, xmm0 [REG, REG]
	andpd	xmm1, xmm0
	## Size 5
	# 0x400b8c:	movq	rax, xmm1 [REG, REG]
	movq	rax, xmm1
	## Size 4
	# 0x400b91:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 5
	# 0x400b95:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 8
	# 0x400b9a:	movsd	xmm0, qword ptr [rip + 0x1ee] [REG, MEM]
	movsd	xmm0,  qword ptr [word ptr [rip + label_62]]
	## Size 4
	# 0x400ba2:	andpd	xmm1, xmm0 [REG, REG]
	andpd	xmm1, xmm0
	## Size 5
	# 0x400ba6:	movq	rax, xmm1 [REG, REG]
	movq	rax, xmm1
	## Size 4
	# 0x400bab:	mov	qword ptr [rbp - 0x30], rax [MEM, REG]
	mov	qword ptr [rbp - 0x30], rax
	## Size 7
	# 0x400baf:	cmp	dword ptr [rbp - 0x14], 0x1fffff [MEM, IMM]
	cmp	dword ptr [rbp - 0x14], 0x1fffff
	## Size 2
	# 0x400bb6:	jg	0x400c17 [IMM <CODEREF>]
	jg	.label_63
	## Size 5
	# 0x400bb8:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400bbd:	addsd	xmm0, xmm0 [REG, REG]
	addsd	xmm0, xmm0
	## Size 5
	# 0x400bc1:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400bc6:	ucomisd	xmm0, xmm1 [REG, REG]
	ucomisd	xmm0, xmm1
	## Size 2
	# 0x400bca:	ja	0x400bd1 [IMM <CODEREF>]
	ja	.label_56
	## Size 5
	# 0x400bcc:	jmp	0x400c77 [IMM <CODEREF>]
	jmp	.label_53
	## Size 5
	# 0x400bd1:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
.label_56:
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400bd6:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400bdb:	subsd	xmm0, xmm1 [REG, REG]
	subsd	xmm0, xmm1
	## Size 5
	# 0x400bdf:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x400be4:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 5
	# 0x400be8:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400bed:	addsd	xmm0, xmm0 [REG, REG]
	addsd	xmm0, xmm0
	## Size 5
	# 0x400bf1:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400bf6:	ucomisd	xmm0, xmm1 [REG, REG]
	ucomisd	xmm0, xmm1
	## Size 2
	# 0x400bfa:	jae	0x400bfe [IMM <CODEREF>]
	jae	.label_59
	## Size 2
	# 0x400bfc:	jmp	0x400c77 [IMM <CODEREF>]
	jmp	.label_53
	## Size 5
	# 0x400bfe:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
.label_59:
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400c03:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400c08:	subsd	xmm0, xmm1 [REG, REG]
	subsd	xmm0, xmm1
	## Size 5
	# 0x400c0c:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x400c11:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 2
	# 0x400c15:	jmp	0x400c77 [IMM <CODEREF>]
	jmp	.label_53
	## Size 5
	# 0x400c17:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
.label_63:
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 8
	# 0x400c1c:	movsd	xmm0, qword ptr [rip + 0x17c] [REG, MEM]
	movsd	xmm0,  qword ptr [word ptr [rip + label_52]]
	## Size 4
	# 0x400c24:	mulsd	xmm1, xmm0 [REG, REG]
	mulsd	xmm1, xmm0
	## Size 5
	# 0x400c28:	movq	rax, xmm1 [REG, REG]
	movq	rax, xmm1
	## Size 4
	# 0x400c2d:	mov	qword ptr [rbp - 8], rax [MEM, REG]
	mov	qword ptr [rbp - 8], rax
	## Size 5
	# 0x400c31:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400c36:	ucomisd	xmm0, qword ptr [rbp - 8] [REG, MEM]
	ucomisd	xmm0, qword ptr [rbp - 8]
	## Size 2
	# 0x400c3b:	jbe	0x400c77 [IMM <CODEREF>]
	jbe	.label_53
	## Size 5
	# 0x400c3d:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400c42:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400c47:	subsd	xmm0, xmm1 [REG, REG]
	subsd	xmm0, xmm1
	## Size 5
	# 0x400c4b:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x400c50:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 5
	# 0x400c54:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400c59:	ucomisd	xmm0, qword ptr [rbp - 8] [REG, MEM]
	ucomisd	xmm0, qword ptr [rbp - 8]
	## Size 2
	# 0x400c5e:	jb	0x400c77 [IMM <CODEREF>]
	jb	.label_53
	## Size 5
	# 0x400c60:	movsd	xmm0, qword ptr [rbp - 0x28] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x28]
	## Size 5
	# 0x400c65:	movsd	xmm1, qword ptr [rbp - 0x30] [REG, MEM]
	movsd	xmm1, qword ptr [rbp - 0x30]
	## Size 4
	# 0x400c6a:	subsd	xmm0, xmm1 [REG, REG]
	subsd	xmm0, xmm1
	## Size 5
	# 0x400c6e:	movq	rax, xmm0 [REG, REG]
	movq	rax, xmm0
	## Size 4
	# 0x400c73:	mov	qword ptr [rbp - 0x28], rax [MEM, REG]
	mov	qword ptr [rbp - 0x28], rax
	## Size 4
	# 0x400c77:	lea	rax, qword ptr [rbp - 0x28] [REG, MEM]
.label_53:
	lea	rax, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400c7b:	lea	rdx, qword ptr [rbp - 0x28] [REG, MEM]
	lea	rdx, qword ptr [rbp - 0x28]
	## Size 2
	# 0x400c7f:	mov	edx, dword ptr [rdx] [REG, MEM]
	mov	edx, dword ptr [rdx]
	## Size 3
	# 0x400c81:	xor	edx, dword ptr [rbp - 0xc] [REG, MEM]
	xor	edx, dword ptr [rbp - 0xc]
	## Size 2
	# 0x400c84:	mov	dword ptr [rax], edx [MEM, REG]
	mov	dword ptr [rax], edx
	## Size 4
	# 0x400c86:	mov	rax, qword ptr [rbp - 0x28] [REG, MEM]
	mov	rax, qword ptr [rbp - 0x28]
	## Size 4
	# 0x400c8a:	mov	qword ptr [rbp - 0x38], rax [MEM, REG]
.label_55:
	mov	qword ptr [rbp - 0x38], rax
	## Size 5
	# 0x400c8e:	movsd	xmm0, qword ptr [rbp - 0x38] [REG, MEM]
	movsd	xmm0, qword ptr [rbp - 0x38]
	## Size 1
	# 0x400c93:	leave	 []
	leave	
	## Size 1
	# 0x400c94:	ret	 []
	ret	
	
	
	.section .plt.got
	.align 32
	# data @ 0x400428
	.label_75:
	.section .text
	.align 16
	# data @ 0x400d12
	.label_76:
	.section .rodata
	.align 32
	# data @ 0x400d20
	.byte 1
	.byte 0
	.byte 2
	# data @ 0x400d23
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400d28
label_9:
	.asciz "The remainder of %lf / %lf is: %lf\n"
	# data @ 0x400d4c
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400d56
	.byte 240
	.byte 63
	# data @ 0x400d58
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400d60
	.globl Zero
	.type Zero, @object
Zero:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 128
	# data @ 0x400d70
label_12:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400d76
	.byte 240
	.byte 63
	# data @ 0x400d78
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400d90
label_62:
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	# data @ 0x400d97
	.byte 127
	# data @ 0x400d98
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400da0
label_52:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	# data @ 0x400da6
	.byte 224
	.byte 63
