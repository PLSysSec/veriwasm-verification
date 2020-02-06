	.intel_syntax noprefix

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 0x30 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_10]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	movsd	qword ptr [rbp - 0x18], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_11]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	movsd	qword ptr [rbp - 0x10], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x10] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mov	rax, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movapd	xmm1, xmm0 # Size:4, Opcode: 0x0f,0x28,0x00,0x00
	mov	qword ptr [rbp - 0x28], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	call	__ieee754_remainder # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x10] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mov	rax, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movapd	xmm2, xmm1 # Size:4, Opcode: 0x0f,0x28,0x00,0x00
	movapd	xmm1, xmm0 # Size:4, Opcode: 0x0f,0x28,0x00,0x00
	mov	qword ptr [rbp - 0x28], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mov	edi, OFFSET FLAT:label_9 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	mov	eax, 3 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl __ieee754_fmod
	.type __ieee754_fmod, @function
__ieee754_fmod:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	movsd	qword ptr [rbp - 0x38], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	qword ptr [rbp - 0x40], xmm1 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x40] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x24], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x40] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0xc], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	and	eax, 0x80000000 # Size:5, Opcode: 0x25,0x00,0x00,0x00
	mov	dword ptr [rbp - 8], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	xor	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x31,0x00,0x00,0x00
	and	dword ptr [rbp - 0x24], 0x7fffffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_23 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x28], 0x7fefffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_23 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	neg	eax # Size:2, Opcode: 0xf7,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	eax, edx # Size:2, Opcode: 0x09,0x00,0x00,0x00
	cmp	eax, 0x7ff00000 # Size:5, Opcode: 0x3d,0x00,0x00,0x00
	jbe	.label_15 # Size:2, Opcode: 0x76,0x00,0x00,0x00
.label_23:
	movsd	xmm1, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x40] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	xmm2, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x40] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm1, xmm2 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	divsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5e,0x00,0x00
	jmp	.label_22 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_15:
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jg	.label_33 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jl	.label_37 # Size:2, Opcode: 0x7c,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jae	.label_42 # Size:2, Opcode: 0x73,0x00,0x00,0x00
.label_37:
	movsd	xmm0, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	jmp	.label_22 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_42:
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jne	.label_33 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	eax, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [(rax * 8) + Zero]] # Size:9, Opcode: 0x0f,0x10,0x00,0x00
	jmp	.label_22 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_33:
	cmp	dword ptr [rbp - 0x28], 0xfffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_13 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x28], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jne	.label_17 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x1c], 0xfffffbed # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_19 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_26:
	sub	dword ptr [rbp - 0x1c], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	shl	dword ptr [rbp - 0x14], 1 # Size:3, Opcode: 0xd1,0x00,0x00,0x00
.label_19:
	cmp	dword ptr [rbp - 0x14], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_26 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	jmp	.label_28 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_17:
	mov	dword ptr [rbp - 0x1c], 0xfffffc02 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shl	eax, 0xb # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_29 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_35:
	sub	dword ptr [rbp - 0x1c], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	shl	dword ptr [rbp - 0x14], 1 # Size:3, Opcode: 0xd1,0x00,0x00,0x00
.label_29:
	cmp	dword ptr [rbp - 0x14], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_35 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	jmp	.label_28 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_13:
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sar	eax, 0x14 # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	sub	eax, 0x3ff # Size:5, Opcode: 0x2d,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x1c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
.label_28:
	cmp	dword ptr [rbp - 0x24], 0xfffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_46 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x24], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jne	.label_48 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x18], 0xfffffbed # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_49 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_14:
	sub	dword ptr [rbp - 0x18], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	shl	dword ptr [rbp - 0x14], 1 # Size:3, Opcode: 0xd1,0x00,0x00,0x00
.label_49:
	cmp	dword ptr [rbp - 0x14], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_14 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	jmp	.label_16 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_48:
	mov	dword ptr [rbp - 0x18], 0xfffffc02 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shl	eax, 0xb # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_39 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_24:
	sub	dword ptr [rbp - 0x18], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	shl	dword ptr [rbp - 0x14], 1 # Size:3, Opcode: 0xd1,0x00,0x00,0x00
.label_39:
	cmp	dword ptr [rbp - 0x14], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_24 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	jmp	.label_16 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_46:
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sar	eax, 0x14 # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	sub	eax, 0x3ff # Size:5, Opcode: 0x2d,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x18], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
.label_16:
	cmp	dword ptr [rbp - 0x1c], 0xfffffc02 # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jl	.label_31 # Size:2, Opcode: 0x7c,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	and	eax, 0xfffff # Size:5, Opcode: 0x25,0x00,0x00,0x00
	or	eax, 0x100000 # Size:5, Opcode: 0x0d,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_34 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_31:
	mov	eax, 0xfffffc02 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x1c] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x2c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x2c], 0x1f # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_44 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, 0x20 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shr	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	or	eax, esi # Size:2, Opcode: 0x09,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	dword ptr [rbp - 0x10], cl # Size:3, Opcode: 0xd3,0x00,0x00,0x00
	jmp	.label_34 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_44:
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, 0x20 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], 0 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
.label_34:
	cmp	dword ptr [rbp - 0x18], 0xfffffc02 # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jl	.label_21 # Size:2, Opcode: 0x7c,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	and	eax, 0xfffff # Size:5, Opcode: 0x25,0x00,0x00,0x00
	or	eax, 0x100000 # Size:5, Opcode: 0x0d,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x24], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_30 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_21:
	mov	eax, 0xfffffc02 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x18] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x2c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x2c], 0x1f # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_32 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, 0x20 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shr	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	or	eax, esi # Size:2, Opcode: 0x09,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x24], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	dword ptr [rbp - 0xc], cl # Size:3, Opcode: 0xd3,0x00,0x00,0x00
	jmp	.label_30 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_32:
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, 0x20 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x24], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0xc], 0 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
.label_30:
	mov	eax, dword ptr [rbp - 0x1c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x18] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x2c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_38 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_25:
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x20], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 4], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jae	.label_27 # Size:2, Opcode: 0x73,0x00,0x00,0x00
	sub	dword ptr [rbp - 0x20], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
.label_27:
	cmp	dword ptr [rbp - 0x20], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jns	.label_36 # Size:2, Opcode: 0x79,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	add	eax, edx # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_38 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_36:
	mov	eax, dword ptr [rbp - 0x20] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	jne	.label_18 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	eax, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [(rax * 8) + Zero]] # Size:9, Opcode: 0x0f,0x10,0x00,0x00
	jmp	.label_22 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_18:
	mov	eax, dword ptr [rbp - 0x20] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	add	eax, edx # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
.label_38:
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	lea	edx, dword ptr [rax - 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x2c], edx # Size:3, Opcode: 0x89,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	jne	.label_25 # Size:6, Opcode: 0x0f,0x85,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x20], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 4], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	cmp	eax, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x3b,0x00,0x00,0x00
	jae	.label_40 # Size:2, Opcode: 0x73,0x00,0x00,0x00
	sub	dword ptr [rbp - 0x20], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
.label_40:
	cmp	dword ptr [rbp - 0x20], 0 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	js	.label_43 # Size:2, Opcode: 0x78,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x20] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
.label_43:
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	jne	.label_50 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	mov	eax, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [(rax * 8) + Zero]] # Size:9, Opcode: 0x0f,0x10,0x00,0x00
	jmp	.label_22 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_47:
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	shr	eax, 0x1f # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	add	eax, edx # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	dword ptr [rbp - 0x18], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
.label_50:
	cmp	dword ptr [rbp - 0x28], 0xfffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jle	.label_47 # Size:2, Opcode: 0x7e,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x18], 0xfffffc02 # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jl	.label_20 # Size:2, Opcode: 0x7c,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	lea	edx, dword ptr [rax - 0x100000] # Size:6, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x18] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, 0x3ff # Size:5, Opcode: 0x05,0x00,0x00,0x00
	shl	eax, 0x14 # Size:3, Opcode: 0xc1,0x00,0x00,0x00
	or	eax, edx # Size:2, Opcode: 0x09,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	edx, dword ptr [rbp - 8] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_45 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_20:
	mov	eax, 0xfffffc02 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x18] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x2c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x2c], 0x14 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_41 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	esi, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shr	esi, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	eax, 0x20 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	or	eax, esi # Size:2, Opcode: 0x09,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	sar	dword ptr [rbp - 0x28], cl # Size:3, Opcode: 0xd3,0x00,0x00,0x00
	jmp	.label_12 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_41:
	cmp	dword ptr [rbp - 0x2c], 0x1f # Size:4, Opcode: 0x83,0x00,0x00,0x00
	jg	.label_52 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	mov	eax, 0x20 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shl	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	shr	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	or	eax, esi # Size:2, Opcode: 0x09,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_12 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_52:
	mov	eax, dword ptr [rbp - 0x2c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, 0x20 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	sar	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x28], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
.label_12:
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x28] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	edx, dword ptr [rbp - 8] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	edx, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_51]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	qword ptr [rbp - 0x38], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
.label_45:
	movsd	xmm0, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
.label_22:
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl __ieee754_remainder
	.type __ieee754_remainder, @function
__ieee754_remainder:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 0x40 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	qword ptr [rbp - 0x30], xmm1 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	lea	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x1c], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x18], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, 4 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x10], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x1c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	and	eax, 0x80000000 # Size:5, Opcode: 0x25,0x00,0x00,0x00
	mov	dword ptr [rbp - 0xc], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	and	dword ptr [rbp - 0x14], 0x7fffffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	and	dword ptr [rbp - 0x1c], 0x7fffffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x14] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	jne	.label_56 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	xmm2, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm1, xmm2 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	divsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5e,0x00,0x00
	jmp	.label_57 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_56:
	cmp	dword ptr [rbp - 0x1c], 0x7fefffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_61 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x14], 0x7fefffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jle	.label_54 # Size:2, Opcode: 0x7e,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x14] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, 0x7ff00000 # Size:5, Opcode: 0x2d,0x00,0x00,0x00
	or	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x0b,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_54 # Size:2, Opcode: 0x74,0x00,0x00,0x00
.label_61:
	movsd	xmm1, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	xmm2, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm1, xmm2 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	divsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5e,0x00,0x00
	jmp	.label_57 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_54:
	cmp	dword ptr [rbp - 0x14], 0x7fdfffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_62 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	addsd	xmm0, xmm0 # Size:4, Opcode: 0x0f,0x58,0x00,0x00
	mov	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movapd	xmm1, xmm0 # Size:4, Opcode: 0x0f,0x28,0x00,0x00
	mov	qword ptr [rbp - 0x38], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x38] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	call	__ieee754_fmod # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 0x28], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
.label_62:
	mov	eax, dword ptr [rbp - 0x1c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x14] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x18] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	sub	eax, dword ptr [rbp - 0x10] # Size:3, Opcode: 0x2b,0x00,0x00,0x00
	or	eax, edx # Size:2, Opcode: 0x09,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	jne	.label_55 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	pxor	xmm1, xmm1 # Size:4, Opcode: 0x0f,0xef,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	jmp	.label_57 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_55:
	movsd	xmm1, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_58]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	andpd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x54,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_58]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	andpd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x54,0x00,0x00
	movsd	qword ptr [rbp - 0x30], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	cmp	dword ptr [rbp - 0x14], 0x1fffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
	jg	.label_59 # Size:2, Opcode: 0x7f,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	addsd	xmm0, xmm0 # Size:4, Opcode: 0x0f,0x58,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	ucomisd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x2e,0x00,0x00
	jbe	.label_53 # Size:6, Opcode: 0x0f,0x86,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	subsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5c,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	addsd	xmm0, xmm0 # Size:4, Opcode: 0x0f,0x58,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	ucomisd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x2e,0x00,0x00
	jb	.label_53 # Size:2, Opcode: 0x72,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	subsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5c,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	jmp	.label_53 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_59:
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_60]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	qword ptr [rbp - 8], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	ucomisd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x2e,0x00,0x00
	jbe	.label_53 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	subsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5c,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	ucomisd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x2e,0x00,0x00
	jb	.label_53 # Size:2, Opcode: 0x72,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x30] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	subsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5c,0x00,0x00
	movsd	qword ptr [rbp - 0x28], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
.label_53:
	lea	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	lea	rdx, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	mov	edx, dword ptr [rdx] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	xor	edx, dword ptr [rbp - 0xc] # Size:3, Opcode: 0x33,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x28] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
.label_57:
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00


	.section .rodata
	.align 16
	.byte 1
	.byte 0
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_9:
	.byte 84
	.byte 104
	.byte 101
	.byte 32
	.byte 114
	.byte 101
	.byte 109
	.byte 97
	.byte 105
	.byte 110
	.byte 100
	.byte 101
	.byte 114
	.byte 32
	.byte 111
	.byte 102
	.byte 32
	.byte 37
	.byte 108
	.byte 102
	.byte 32
	.byte 47
	.byte 32
	.byte 37
	.byte 108
	.byte 102
	.byte 32
	.byte 105
	.byte 115
	.byte 58
	.byte 32
	.byte 37
	.byte 108
	.byte 102
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_10:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 20
	.byte 64
label_11:
	.byte 154
	.byte 153
	.byte 153
	.byte 153
	.byte 153
	.byte 153
	.byte 241
	.byte 63
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 63
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
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
label_51:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 63
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
label_58:
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 127
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_60:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 224
	.byte 63

	.section .data
	.align 8
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

	.section .bss
	.align 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_3:
	.byte 0
		.globl _end
	.type _end, @notype
_end:
