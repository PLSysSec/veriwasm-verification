	.intel_syntax noprefix

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	mov	rax, qword ptr [rsi + 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movsx	eax, byte ptr [rax] # Size:3, Opcode: 0x0f,0xbe,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	sub	edx, 0x30 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	je	label_9 # Size:6, Opcode: 0x0f,0x84,0x00,0x00
	sub	eax, 0x31 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	cmp	eax, 7 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	jbe	label_4 # Size:6, Opcode: 0x0f,0x86,0x00,0x00
	mov	ecx, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movdqa	xmm1,  xmmword ptr [word ptr [rip + label_8]] # Size:8, Opcode: 0x0f,0x6f,0x00,0x00
	shr	ecx, 1 # Size:2, Opcode: 0xd1,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	nop	dword ptr [rax] # Size:4, Opcode: 0x0f,0x1f,0x00,0x00
label_3:
	add	eax, 1 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	psllq	xmm1, 1 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	cmp	eax, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jb	label_3 # Size:2, Opcode: 0x72,0x00,0x00,0x00
	movdqa	xmm4, xmm1 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	mov	ecx, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movdqa	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	movdqa	xmm2, xmm1 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	psrldq	xmm4, 8 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	and	ecx, 0xfffffffe # Size:3, Opcode: 0x83,0x00,0x00,0x00
	movdqa	xmm3, xmm4 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	cmp	edx, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	pmuludq	xmm0, xmm4 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	psrlq	xmm2, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	psrlq	xmm3, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	pmuludq	xmm2, xmm4 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	pmuludq	xmm1, xmm3 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	paddq	xmm2, xmm1 # Size:4, Opcode: 0x0f,0xd4,0x00,0x00
	psllq	xmm2, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	paddq	xmm0, xmm2 # Size:4, Opcode: 0x0f,0xd4,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	je	label_7 # Size:2, Opcode: 0x74,0x00,0x00,0x00
label_5:
	lea	esi, dword ptr [rcx + 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	esi, dword ptr [rcx + 2] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	esi, dword ptr [rcx + 3] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	esi, dword ptr [rcx + 4] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	esi, dword ptr [rcx + 5] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	esi, dword ptr [rcx + 6] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, esi # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	add	ecx, 7 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edx, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	label_6 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00
label_9:
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
label_6:
	ret	 # Size:2, Opcode: 0xc3,0x00,0x00,0x00
label_7:
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00
label_4:
	xor	ecx, ecx # Size:2, Opcode: 0x31,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	jmp	label_5 # Size:2, Opcode: 0xeb,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl pow2
	.type pow2, @function
pow2:
	test	edi, edi # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_18 # Size:6, Opcode: 0x0f,0x84,0x00,0x00
	lea	eax, dword ptr [rdi - 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	cmp	eax, 7 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	jbe	.label_20 # Size:6, Opcode: 0x0f,0x86,0x00,0x00
	mov	edx, edi # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movdqa	xmm0,  xmmword ptr [word ptr [rip + label_8]] # Size:8, Opcode: 0x0f,0x6f,0x00,0x00
	shr	edx, 1 # Size:2, Opcode: 0xd1,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	nop	word ptr [rax + rax] # Size:6, Opcode: 0x0f,0x1f,0x00,0x00
.label_21:
	add	eax, 1 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	psllq	xmm0, 1 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	cmp	eax, edx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jb	.label_21 # Size:2, Opcode: 0x72,0x00,0x00,0x00
	movdqa	xmm4, xmm0 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	mov	edx, edi # Size:2, Opcode: 0x89,0x00,0x00,0x00
	movdqa	xmm1, xmm0 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	movdqa	xmm2, xmm0 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	psrldq	xmm4, 8 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	and	edx, 0xfffffffe # Size:3, Opcode: 0x83,0x00,0x00,0x00
	movdqa	xmm3, xmm4 # Size:4, Opcode: 0x0f,0x6f,0x00,0x00
	cmp	edi, edx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	pmuludq	xmm1, xmm4 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	psrlq	xmm2, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	psrlq	xmm3, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	pmuludq	xmm2, xmm4 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	pmuludq	xmm0, xmm3 # Size:4, Opcode: 0x0f,0xf4,0x00,0x00
	paddq	xmm2, xmm0 # Size:4, Opcode: 0x0f,0xd4,0x00,0x00
	psllq	xmm2, 0x20 # Size:5, Opcode: 0x0f,0x73,0x00,0x00
	paddq	xmm1, xmm2 # Size:4, Opcode: 0x0f,0xd4,0x00,0x00
	movq	rax, xmm1 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	je	.label_23 # Size:2, Opcode: 0x74,0x00,0x00,0x00
.label_22:
	lea	ecx, dword ptr [rdx + 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	ecx, dword ptr [rdx + 2] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	ecx, dword ptr [rdx + 3] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	ecx, dword ptr [rdx + 4] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	ecx, dword ptr [rdx + 5] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	lea	ecx, dword ptr [rdx + 6] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	cmp	edi, ecx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	jbe	.label_19 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	add	rax, rax # Size:3, Opcode: 0x01,0x00,0x00,0x00
	add	edx, 7 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	lea	rcx, qword ptr [rax + rax] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
	cmp	edi, edx # Size:2, Opcode: 0x39,0x00,0x00,0x00
	cmova	rax, rcx # Size:4, Opcode: 0x0f,0x47,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00
.label_18:
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
.label_19:
	ret	 # Size:2, Opcode: 0xc3,0x00,0x00,0x00
.label_23:
	ret	 # Size:2, Opcode: 0xc3,0x00,0x00,0x00
.label_20:
	xor	edx, edx # Size:2, Opcode: 0x31,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	jmp	.label_22 # Size:2, Opcode: 0xeb,0x00,0x00,0x00


	.section .comment
	.align 32
label_26:
	.byte 127
	.byte 69
	.byte 76
	.byte 70
	.byte 2
	.byte 1
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 3
	.byte 0
	.byte 62
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 208
	.byte 5
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	label_29:

	.section .symtab
	.align 32
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
	.byte 64
	.byte 56
	.byte 9
	.byte 64
	.byte 28
	.byte 0
	.byte 27
	.byte 0
	.byte 6
	.byte 0
	.byte 0
	.byte 0
	.byte 5
	.byte 0
	.quad label_26
	.quad label_26
	.quad label_26
	.byte 0
	.byte 0
	.byte 248
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 248
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 3
	.byte 0
	.byte 0
	.byte 0
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 56
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 56
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 56
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 28
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 28
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 5
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
	.byte 0
	.byte 0
	.byte 0
	.byte 216
	.byte 9
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 216
	.byte 9
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 6
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 13
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240

	.section .shstrtab
	.align 32
	label_31:

	.section .symtab
	.align 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 32
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 40
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 6
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 14
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 14
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 14
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 192
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 192
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 84
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 84
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 84
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 68
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 68
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 80
	.byte 229
	.byte 116
	.byte 100
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 128
	.byte 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 128
	.byte 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 128
	.byte 8
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 68
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 68
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 81
	.byte 229
	.byte 116
	.byte 100
	.byte 6
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

	.section .strtab
	.align 32
	label_30:

	.section .symtab
	.align 32
	.byte 16
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 82
	.byte 229
	.byte 116
	.byte 100
	.byte 4
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 13
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 16
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 16
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0

	.section .rodata
	.align 32
	.byte 1
	.byte 0
	.byte 2
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
label_8:
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 1
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0

	.section .data
	.align 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0

	.section .bss
	.align 16
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
		.globl _end
	.type _end, @notype
_end:
