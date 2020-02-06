	.intel_syntax noprefix

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 0x10 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	mov	dword ptr [rbp - 4], 0x15 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	edi, OFFSET FLAT:label_9 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
	add	eax, eax # Size:2, Opcode: 0x01,0x00,0x00,0x00
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00


	.section .rodata
	.align 16
	.byte 1
	.byte 0
	.byte 2
	.byte 0
label_9:
	.byte 82
	.byte 101
	.byte 116
	.byte 117
	.byte 114
	.byte 110
	.byte 58
	.byte 32
	.byte 37
	.byte 105
	.byte 10
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
