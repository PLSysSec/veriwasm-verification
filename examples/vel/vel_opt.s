	.intel_syntax noprefix

	.section	.text
	.align	32
	.globl main
	.type main, @function
main:
	sub	rsp, 8 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	call	fegetround # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	lea	rsi,  qword ptr [word ptr [rip + label_3]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	call	__printf_chk # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_9]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	lea	rsi,  qword ptr [word ptr [rip + label_10]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	__printf_chk # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_6]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	lea	rsi,  qword ptr [word ptr [rip + label_7]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	__printf_chk # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movsd	xmm0,  qword ptr [word ptr [rip + label_4]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	lea	rsi,  qword ptr [word ptr [rip + label_5]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	mov	eax, 1 # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	call	__printf_chk # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	call	updateDisplayVelocity # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	lea	rsi,  qword ptr [word ptr [rip + label_8]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	mov	edx, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
	mov	edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	call	__printf_chk # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	xor	eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
	add	rsp, 8 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl rawToDouble
	.type rawToDouble, @function
rawToDouble:
	mov	qword ptr [rsp - 8], rdi # Size:5, Opcode: 0x89,0x00,0x00,0x00
	movsd	xmm0, qword ptr [rsp - 8] # Size:6, Opcode: 0x0f,0x10,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl get_current_velocity
	.type get_current_velocity, @function
get_current_velocity:
	movsd	xmm0,  qword ptr [word ptr [rip + label_9]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl get_current_braking_force
	.type get_current_braking_force, @function
get_current_braking_force:
	movsd	xmm0,  qword ptr [word ptr [rip + label_6]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl get_current_accel_force
	.type get_current_accel_force, @function
get_current_accel_force:
	movsd	xmm0,  qword ptr [word ptr [rip + label_4]] # Size:8, Opcode: 0x0f,0x10,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl throw_velocity_exception
	.type throw_velocity_exception, @function
throw_velocity_exception:
	lea	rdi,  qword ptr [word ptr [rip + label_19]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
	jmp	puts # Size:5, Opcode: 0xe9,0x00,0x00,0x00

	.section	.text
	.align	32
	.globl updateDisplayVelocity
	.type updateDisplayVelocity, @function
updateDisplayVelocity:
	sub	rsp, 0x18 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	call	get_current_velocity # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movsd	qword ptr [rsp], xmm0 # Size:5, Opcode: 0x0f,0x11,0x00,0x00
	call	get_current_braking_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	movsd	qword ptr [rsp + 8], xmm0 # Size:6, Opcode: 0x0f,0x11,0x00,0x00
	call	get_current_accel_force # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	subsd	xmm0, qword ptr [rsp + 8] # Size:6, Opcode: 0x0f,0x5c,0x00,0x00
	divsd	xmm0,  qword ptr [word ptr [rip + label_21]] # Size:8, Opcode: 0x0f,0x5e,0x00,0x00
	mulsd	xmm0,  qword ptr [word ptr [rip + label_22]] # Size:8, Opcode: 0x0f,0x59,0x00,0x00
	addsd	xmm0, qword ptr [rsp] # Size:5, Opcode: 0x0f,0x58,0x00,0x00
	ucomisd	xmm0,  qword ptr [word ptr [rip + label_23]] # Size:8, Opcode: 0x0f,0x2e,0x00,0x00
	ja	.label_24 # Size:2, Opcode: 0x77,0x00,0x00,0x00
	cvttsd2si	eax, xmm0 # Size:4, Opcode: 0x0f,0x2c,0x00,0x00
.label_20:
	add	rsp, 0x18 # Size:4, Opcode: 0x83,0x00,0x00,0x00
	ret	 # Size:1, Opcode: 0xc3,0x00,0x00,0x00
.label_24:
	call	throw_velocity_exception # Size:5, Opcode: 0xe8,0x00,0x00,0x00
	mov	eax, 0xffffffff # Size:5, Opcode: 0xb8,0x00,0x00,0x00
	jmp	.label_20 # Size:2, Opcode: 0xeb,0x00,0x00,0x00


	.section .comment
	.align 32
label_27:
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
	.byte 192
	.byte 6
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
	label_30:

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
	.quad label_27
	.quad label_27
	.quad label_27
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
	.byte 16
	.byte 12
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 16
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
	label_33:

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
	.byte 24
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 24
	.byte 10
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 24
	.byte 10
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
	label_32:

	.section .symtab
	.align 32
	.label_31:

	.section .rodata
	.align 32
	.byte 1
	.byte 0
	.byte 2
	.byte 0
label_19:
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
label_3:
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
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_10:
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
label_7:
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
label_5:
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
label_8:
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
label_9:
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 255
	.byte 191
	.byte 43
	.byte 64
label_6:
	.quad 0x41fbfe12adb01c80
label_4:
	.byte 212
	.byte 252
	.byte 8
	.byte 120
	.byte 19
	.byte 1
	.byte 244
	.byte 65
	.byte 252
	.byte 169
	.byte 241
	.byte 210
	.byte 77
	.byte 98
	.byte 80
	.byte 63
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 143
	.byte 64
	.byte 230
	.byte 63
	.byte 164
	.byte 223
	.byte 190
	.byte 14
	.byte 77
	.byte 64
label_21:
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 64
	.byte 143
	.byte 64
label_22:
	.quad 0x3f50624dd2f1a9fc
label_23:
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
