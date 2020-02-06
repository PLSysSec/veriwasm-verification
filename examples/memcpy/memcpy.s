	.intel_syntax noprefix

	.section	.text
	.align	16
	.globl swap
	.type swap, @function
swap:
	sub	rsp, 0x28 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	rax, qword ptr fs:[0x28] # Size:9, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rsp + 0x18], rax # Size:5, Opcode: 0x89,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	mov	rdx, qword ptr [rdi] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rsp], rdx # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movzx	eax, byte ptr [rdi + 8] # Size:4, Opcode: 0x0f,0xb6,0x00,0x00
	mov	byte ptr [rsp + 8], al # Size:4, Opcode: 0x88,0x00,0x00,0x00
	mov	rcx, qword ptr [rsi] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rdi], rcx # Size:3, Opcode: 0x89,0x00,0x00,0x00
	movzx	ecx, byte ptr [rsi + 8] # Size:4, Opcode: 0x0f,0xb6,0x00,0x00
	mov	byte ptr [rdi + 8], cl # Size:3, Opcode: 0x88,0x00,0x00,0x00
	mov	qword ptr [rsi], rdx # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	byte ptr [rsi + 8], al # Size:3, Opcode: 0x88,0x00,0x00,0x00
	mov	rax, qword ptr [rsp + 0x18] # Size:5, Opcode: 0x8b,0x00,0x00,0x00
	xor	rax, qword ptr fs:[0x28] # Size:9, Opcode: 0x33,0x00,0x00,0x00
	je	.label_9 # Size:2, Opcode: 0x74,0x00,0x00,0x00
	call	__stack_chk_fail # Size:5, Opcode: 0xe8,0x00,0x00,0x00
.label_9:
	add	rsp, 0x28 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00


	.section .rodata
	.align 32
	.byte 1
	.byte 0
	.byte 2
	.byte 0

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
