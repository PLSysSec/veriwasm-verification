	.intel_syntax noprefix

	.section	.text
	.align	16
	.globl rawToDouble
	.type rawToDouble, @function
rawToDouble:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	qword ptr [rbp - 0x18], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
	mov	rax, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
.label_28:
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl get_current_velocity
	.type get_current_velocity, @function
get_current_velocity:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 8 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	movabs	rdi, 0x402bbfffffffffff # Size:10, Opcode: 0xbf,0x00,0x00,0x00
	call	rawToDouble # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl get_current_braking_force
	.type get_current_braking_force, @function
get_current_braking_force:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 8 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	movabs	rdi, 0x41fbfe12adb01c80 # Size:10, Opcode: 0xbf,0x00,0x00,0x00
	call	rawToDouble # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl get_current_accel_force
	.type get_current_accel_force, @function
get_current_accel_force:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 8 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	movabs	rdi, 0x41f401137808fcd4 # Size:10, Opcode: 0xbf,0x00,0x00,0x00
	call	rawToDouble # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 8], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl throw_velocity_exception
	.type throw_velocity_exception, @function
throw_velocity_exception:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_11]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	call	puts # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	nop	 # Size:1, Opcode: 0x90,0x00,0x00,0x00
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	call	fegetround # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_12]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	call	get_current_velocity # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_15]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	call	get_current_braking_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_14]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	call	get_current_accel_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_13]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	call	updateDisplayVelocity # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	lea	rdi,  qword ptr [word ptr [rip + label_16]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	printf # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	eax, 0 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	pop	rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	16
	.globl updateDisplayVelocity
	.type updateDisplayVelocity, @function
updateDisplayVelocity:
	push	rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
	mov	rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
	sub	rsp, 0x30 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	call	get_current_velocity # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 0x20], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	call	get_current_braking_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 0x18], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	call	get_current_accel_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movq	rax, xmm0 # Size:5, Opcode: 0x0f,0x7e,0x00,0x00
	mov	qword ptr [rbp - 0x10], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
	pxor	xmm0, xmm0 # Size:4, Opcode: 0x0f,0xef,0x00,0x00
	movsd	qword ptr [rbp - 8], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	mov	dword ptr [rbp - 0x24], 0 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 0x10] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	subsd	xmm0, qword ptr [rbp - 0x18] # Size:5, Opcode: 0x0f,0x5c,0x00,0x00
	movsd	xmm1,  qword ptr [word ptr [rip + label_18]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	divsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x5e,0x00,0x00
	movsd	xmm1,  qword ptr [word ptr [rip + label_19]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	mulsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x59,0x00,0x00
	movsd	xmm1, qword ptr [rbp - 0x20] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	addsd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x58,0x00,0x00
	movsd	qword ptr [rbp - 8], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	movsd	xmm1,  qword ptr [word ptr [rip + label_20]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	ucomisd	xmm0, xmm1 # Size:4, Opcode: 0x0f,0x2e,0x00,0x00
	jbe	.label_21 # Size:2, Opcode: 0x76,0x00,0x00,0x00
	call	throw_velocity_exception # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	eax, 0xffffffff # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	jmp	.label_17 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_21:
	movsd	xmm0, qword ptr [rbp - 8] # Size:5, Opcode: 0x0f,0x10,0x00,0x00
	cvttsd2si	eax, xmm0 # Size:4, Opcode: 0x0f,0x2c,0x00,0x00
	mov	dword ptr [rbp - 0x24], eax # Size:3, Opcode: 0x89,0x00,0x00,0x00
	mov	eax, dword ptr [rbp - 0x24] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
.label_17:
	leave	 # Size:1, Opcode: 0xc9,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00


	.section .comment
	.align 32
label_24:
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
	.byte 240
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
	label_27:

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
	.byte 29
	.byte 0
	.byte 28
	.byte 0
	.byte 6
	.byte 0
	.byte 0
	.byte 0
	.byte 5
	.byte 0
	.quad label_24
	.quad label_24
	.quad label_24
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
	.byte 120
	.byte 12
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 120
	.byte 12
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
	.byte 152
	.byte 13
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 152
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0

	.section .shstrtab
	.align 32
	label_30:

	.section .symtab
	.align 32
	.byte 152
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 120
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 128
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
	.byte 168
	.byte 13
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 168
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 168
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 2
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
	.byte 64
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 108
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 108
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
	.byte 0
	.byte 0
	.byte 0
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
	.byte 152
	.byte 13
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 152
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 152
	.byte 13
	.byte 32
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 104
	.byte 2
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 104
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

	.section .strtab
	.align 32
	label_29:

	.section .symtab
	.align 32
	.label_28:

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
label_11:
	.byte 42
	.byte 42
	.byte 32
	.byte 86
	.byte 69
	.byte 76
	.byte 79
	.byte 67
	.byte 73
	.byte 84
	.byte 89
	.byte 32
	.byte 69
	.byte 88
	.byte 67
	.byte 69
	.byte 80
	.byte 84
	.byte 73
	.byte 79
	.byte 78
	.byte 32
	.byte 42
	.byte 42
label_12:
	.byte 82
	.byte 79
	.byte 85
	.byte 78
	.byte 68
	.byte 73
	.byte 78
	.byte 71
	.byte 95
	.byte 77
	.byte 79
	.byte 68
	.byte 69
	.byte 32
	.byte 40
	.byte 48
	.byte 63
	.byte 41
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 61
	.byte 32
	.byte 37
	.byte 100
	.byte 10
	.byte 0
	.byte 0
label_15:
	.byte 67
	.byte 85
	.byte 82
	.byte 82
	.byte 69
	.byte 78
	.byte 84
	.byte 95
	.byte 86
	.byte 69
	.byte 76
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 61
	.byte 32
	.byte 37
	.byte 102
	.byte 32
	.byte 109
	.byte 47
	.byte 115
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_14:
	.byte 67
	.byte 85
	.byte 82
	.byte 82
	.byte 69
	.byte 78
	.byte 84
	.byte 95
	.byte 66
	.byte 82
	.byte 69
	.byte 65
	.byte 75
	.byte 73
	.byte 78
	.byte 71
	.byte 95
	.byte 70
	.byte 79
	.byte 82
	.byte 67
	.byte 69
	.byte 32
	.byte 61
	.byte 32
	.byte 37
	.byte 102
	.byte 32
	.byte 78
	.byte 10
	.byte 0
label_13:
	.byte 67
	.byte 85
	.byte 82
	.byte 82
	.byte 69
	.byte 78
	.byte 84
	.byte 95
	.byte 65
	.byte 67
	.byte 67
	.byte 69
	.byte 76
	.byte 95
	.byte 70
	.byte 79
	.byte 82
	.byte 67
	.byte 69
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 61
	.byte 32
	.byte 37
	.byte 102
	.byte 32
	.byte 78
	.byte 10
	.byte 0
label_16:
	.byte 68
	.byte 73
	.byte 83
	.byte 80
	.byte 76
	.byte 65
	.byte 89
	.byte 95
	.byte 86
	.byte 69
	.byte 76
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 32
	.byte 61
	.byte 32
	.byte 37
	.byte 100
	.byte 32
	.byte 109
	.byte 47
	.byte 115
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 230
	.byte 63
	.byte 164
	.byte 223
	.byte 190
	.byte 14
	.byte 77
	.byte 64
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 143
	.byte 64
	.byte 252
	.byte 169
	.byte 241
	.byte 210
	.byte 77
	.byte 98
	.byte 80
	.byte 63
label_18:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 143
	.byte 64
label_19:
	.quad 0x3f50624dd2f1a9fc
label_20:
	.quad 0x404d0ebedfa43fe6

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
