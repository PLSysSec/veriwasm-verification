	.intel_syntax noprefix

	.section	.text
	.align	32
	.globl ssl_SetupCAList
	.type ssl_SetupCAList, @function
ssl_SetupCAList:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 8], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl main
	.type main, @function
main:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl ssl_GetCertificateRequestCAs
	.type ssl_GetCertificateRequestCAs, @function
ssl_GetCertificateRequestCAs:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 0x40 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x28], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x30], rsi # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x38], rdx # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x40], rcx # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], 0 # Size:6, Opcode: 0xc7,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rax], 0 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x40] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], 0 # Size:6, Opcode: 0xc7,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rax + 0x5d0] # Size:7, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	cmp	qword ptr [rbp - 8], 0 # Size:5, Opcode: 0x83,0x00,0x00,0x00
	jne	.label_10 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x28] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	call	ssl_SetupCAList # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_12 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	mov	eax, 0xffffffff # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	jmp	.label_14 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_12:
	mov	rax,  qword ptr [word ptr [rip + label_15]] # Size:7, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
.label_10:
	cmp	qword ptr [rbp - 8], 0 # Size:5, Opcode: 0x83,0x00,0x00,0x00
	je	.label_11 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rdx, qword ptr [rax + 0x10] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rax], rdx # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	eax, dword ptr [rax + 8] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x40] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
.label_11:
	mov	dword ptr [rbp - 0x14], 0 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x38] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rax] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x10], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_13 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_16:
	mov	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	edx, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x10] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	eax, dword ptr [rax + 0x10] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, edx # Size:2, Opcode: 0x01,0x00,0x00,0x00
	lea	edx, dword ptr [rax + 2] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x30] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	dword ptr [rax], edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	add	dword ptr [rbp - 0x14], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	add	qword ptr [rbp - 0x10], 0x18 # Size:5, Opcode: 0x83,0x00,0x00,0x00
.label_13:
	mov	rax, qword ptr [rbp - 0x40] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
	cmp	dword ptr [rbp - 0x14], eax # Size:3, Opcode: 0x39,0x00,0x00,0x00
	jb	.label_16 # Size:2, Opcode: 0x72,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
.label_14:
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl ssl_FindServerCert
	.type ssl_FindServerCert, @function
ssl_FindServerCert:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x18], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	dword ptr [rbp - 0x1c], esi # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x28], rdx # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rax + 0x338] # Size:7, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x10], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	jmp	.label_17 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_18:
	mov	rax, qword ptr [rbp - 0x10] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movzx	eax, word ptr [rax + 0x10] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
	movzx	edx, ax # Size:3, Opcode: 0x0f,0xb7,0x00,0x00
	mov	eax, dword ptr [rbp - 0x1c] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	ecx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	sar	edx, cl # Size:2, Opcode: 0xd3,0x00,0x00,0x00
	mov	eax, edx # Size:2, Opcode: 0x89,0x00,0x00,0x00
	and	eax, 1 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_19 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	movzx	eax, word ptr [rax + 0x10] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
	movzx	eax, ax # Size:3, Opcode: 0x0f,0xb7,0x00,0x00
	and	eax, 0x70 # Size:3, Opcode: 0x83,0x00,0x00,0x00
	test	eax, eax # Size:2, Opcode: 0x85,0x00,0x00,0x00
	je	.label_21 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	cmp	qword ptr [rbp - 0x28], 0 # Size:5, Opcode: 0x83,0x00,0x00,0x00
	je	.label_21 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rax + 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	cmp	qword ptr [rbp - 0x28], rax # Size:4, Opcode: 0x39,0x00,0x00,0x00
	jne	.label_23 # Size:2, Opcode: 0x75,0x00,0x00,0x00
.label_21:
	mov	rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	jmp	.label_22 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_19:
	nop	 # Size:1, Opcode: 0x90,0x00,0x00,0x00
	jmp	.label_20 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_23:
	nop	 # Size:1, Opcode: 0x90,0x00,0x00,0x00
.label_20:
	mov	rax, qword ptr [rbp - 0x10] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	rax, qword ptr [rax] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x10], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
.label_17:
	mov	rax, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	add	rax, 0x338 # Size:6, Opcode: 0x05,0x00,0x00,0x00
	cmp	qword ptr [rbp - 0x10], rax # Size:4, Opcode: 0x39,0x00,0x00,0x00
	jne	.label_18 # Size:2, Opcode: 0x75,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
.label_22:
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00




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
	.byte 45
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 61
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 240
	.byte 61
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
	.label_29:

	.section .rodata
	.align 32
	.byte 1
	.byte 0
	.byte 2
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
label_15:
	.byte 0
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

