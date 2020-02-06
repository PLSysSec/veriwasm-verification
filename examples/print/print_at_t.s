	.section	.init
	.align	8
	#Procedure 0x4003c8

	# 0x4003c8:	subq	$8, %rsp [IMM, REG]
	.globl _init
	.type _init, @function
_init:
	subq	$8, %rsp
	# 0x4003cc:	movq	0x200c25(%rip), %rax [MEM, REG]
	movq	.label_23(%rip),  %rax
	# 0x4003d3:	testq	%rax, %rax [REG, REG]
	testq	%rax, %rax
	# 0x4003d6:	je	0x4003dd [IMM <CODEREF>]
	je	.label_24
	# 0x4003d8:	callq	0x400420 [IMM <CODEREF>]
	callq	.label_25
	# 0x4003dd:	addq	$8, %rsp [IMM, REG]
.label_24:
	addq	$8, %rsp
	# 0x4003e1:	retq	 []
	retq	
	.section	.plt.got
	.align	32
	#Procedure 0x400420

	# 0x400420:	jmpq	*0x200bd2(%rip) [MEM]
.label_25:
	jmpq	*.label_23(%rip)
	.section	.text
	.align	16
	#Procedure 0x400430
	.globl _start
	.type _start, @function
_start:

	# 0x400430:	xorl	%ebp, %ebp [REG, REG]
	xorl	%ebp, %ebp
	# 0x400432:	movq	%rdx, %r9 [REG, REG]
	movq	%rdx, %r9
	# 0x400435:	popq	%rsi [REG]
	popq	%rsi
	# 0x400436:	movq	%rsp, %rdx [REG, REG]
	movq	%rsp, %rdx
	# 0x400439:	andq	$0xfffffff0, %rsp [IMM, REG]
	andq	$0xfffffff0, %rsp
	# 0x40043d:	pushq	%rax [REG]
	pushq	%rax
	# 0x40043e:	pushq	%rsp [REG]
	pushq	%rsp
	# 0x40043f:	movq	$0x4005c0, %r8 [IMM <CODEREF>, REG]
	movq	$__libc_csu_fini,  %r8
	# 0x400446:	movq	$0x400550, %rcx [IMM <CODEREF>, REG]
	movq	$__libc_csu_init,  %rcx
	# 0x40044d:	movq	$0x400526, %rdi [IMM <CODEREF>, REG]
	movq	$main,  %rdi
	# 0x400454:	callq	0x400410 [IMM <CODEREF>]
	callq	__libc_start_main
	.section	.text
	.align	16
	#Procedure 0x400459
	.globl sub_400459
	.type sub_400459, @function
sub_400459:

	# 0x400459:	hlt	 []
	hlt	
	.section	.text
	.align	16
	#Procedure 0x400460

	# 0x400460:	movl	$0x60103f, %eax [IMM <DATAREF>, REG]
	.globl deregister_tm_clones
	.type deregister_tm_clones, @function
deregister_tm_clones:
	movl	$label_26,  %eax
	# 0x400465:	pushq	%rbp [REG]
	pushq	%rbp
	# 0x400466:	subq	$0x601038, %rax [IMM <DATAREF>, REG]
	subq	__TMC_END__,  %rax
	# 0x40046c:	cmpq	$0xe, %rax [IMM, REG]
	cmpq	$0xe, %rax
	# 0x400470:	movq	%rsp, %rbp [REG, REG]
	movq	%rsp, %rbp
	# 0x400473:	jbe	0x400490 [IMM <CODEREF>]
	jbe	.label_27
	# 0x400475:	movl	$0, %eax [IMM, REG]
	movl	$0, %eax
	# 0x40047a:	testq	%rax, %rax [REG, REG]
	testq	%rax, %rax
	# 0x40047d:	je	0x400490 [IMM <CODEREF>]
	je	.label_27
	# 0x40047f:	popq	%rbp [REG]
	popq	%rbp
	# 0x400480:	movl	$0x601038, %edi [IMM <DATAREF>, REG]
	movl	$__TMC_END__,  %edi
	# 0x400485:	jmpq	*%rax [REG]
	jmpq	*%rax
	# 0x400487:	nopw	(%rax, %rax) [MEM]
	nopw	(%rax, %rax)
	# 0x400490:	popq	%rbp [REG]
.label_27:
	popq	%rbp
	# 0x400491:	retq	 []
	retq	
	.section	.text
	.align	16
	#Procedure 0x4004a0

	# 0x4004a0:	movl	$0x601038, %esi [IMM <DATAREF>, REG]
	.globl register_tm_clones
	.type register_tm_clones, @function
register_tm_clones:
	movl	$__TMC_END__,  %esi
	# 0x4004a5:	pushq	%rbp [REG]
	pushq	%rbp
	# 0x4004a6:	subq	$0x601038, %rsi [IMM <DATAREF>, REG]
	subq	$__TMC_END__,  %rsi
	# 0x4004ad:	sarq	$3, %rsi [IMM, REG]
	sarq	$3, %rsi
	# 0x4004b1:	movq	%rsp, %rbp [REG, REG]
	movq	%rsp, %rbp
	# 0x4004b4:	movq	%rsi, %rax [REG, REG]
	movq	%rsi, %rax
	# 0x4004b7:	shrq	$0x3f, %rax [IMM, REG]
	shrq	$0x3f, %rax
	# 0x4004bb:	addq	%rax, %rsi [REG, REG]
	addq	%rax, %rsi
	# 0x4004be:	sarq	$1, %rsi [IMM, REG]
	sarq	$1, %rsi
	# 0x4004c1:	je	0x4004d8 [IMM <CODEREF>]
	je	.label_28
	# 0x4004c3:	movl	$0, %eax [IMM, REG]
	movl	$0, %eax
	# 0x4004c8:	testq	%rax, %rax [REG, REG]
	testq	%rax, %rax
	# 0x4004cb:	je	0x4004d8 [IMM <CODEREF>]
	je	.label_28
	# 0x4004cd:	popq	%rbp [REG]
	popq	%rbp
	# 0x4004ce:	movl	$0x601038, %edi [IMM <DATAREF>, REG]
	movl	$__TMC_END__,  %edi
	# 0x4004d3:	jmpq	*%rax [REG]
	jmpq	*%rax
	# 0x4004d5:	nopl	(%rax) [MEM]
	nopl	(%rax)
	# 0x4004d8:	popq	%rbp [REG]
.label_28:
	popq	%rbp
	# 0x4004d9:	retq	 []
	retq	
	.section	.text
	.align	16
	#Procedure 0x4004e0

	# 0x4004e0:	cmpb	$0, 0x200b51(%rip) [IMM, MEM]
	.globl __do_global_dtors_aux
	.type __do_global_dtors_aux, @function
__do_global_dtors_aux:
	cmpb	$0, __TMC_END__(%rip)
	# 0x4004e7:	jne	0x4004fa [IMM <CODEREF>]
	jne	.label_29
	# 0x4004e9:	pushq	%rbp [REG]
	pushq	%rbp
	# 0x4004ea:	movq	%rsp, %rbp [REG, REG]
	movq	%rsp, %rbp
	# 0x4004ed:	callq	0x400460 [IMM <CODEREF>]
	callq	deregister_tm_clones
	# 0x4004f2:	popq	%rbp [REG]
	popq	%rbp
	# 0x4004f3:	movb	$1, 0x200b3e(%rip) [IMM, MEM]
	movb	$1, __TMC_END__(%rip)
	# 0x4004fa:	retq	 []
.label_29:
	retq	
	.section	.text
	.align	16
	#Procedure 0x400500

	# 0x400500:	movl	$0x600e20, %edi [IMM <DATAREF>, REG]
	.globl frame_dummy
	.type frame_dummy, @function
frame_dummy:
	movl	$__JCR_END__,  %edi
	# 0x400505:	cmpq	$0, (%rdi) [IMM, MEM]
	cmpq	$0, (%rdi)
	# 0x400509:	jne	0x400510 [IMM <CODEREF>]
	jne	.label_30
	# 0x40050b:	jmp	0x4004a0 [IMM <CODEREF>]
.label_31:
	jmp	register_tm_clones
	# 0x400510:	movl	$0, %eax [IMM, REG]
.label_30:
	movl	$0, %eax
	# 0x400515:	testq	%rax, %rax [REG, REG]
	testq	%rax, %rax
	# 0x400518:	je	0x40050b [IMM <CODEREF>]
	je	.label_31
	# 0x40051a:	pushq	%rbp [REG]
	pushq	%rbp
	# 0x40051b:	movq	%rsp, %rbp [REG, REG]
	movq	%rsp, %rbp
	# 0x40051e:	callq	*%rax [REG]
	callq	*%rax
	# 0x400520:	popq	%rbp [REG]
	popq	%rbp
	# 0x400521:	jmp	0x4004a0 [IMM <CODEREF>]
	jmp	register_tm_clones
	.section	.text
	.align	16
	#Procedure 0x400526

	# 0x400526:	pushq	%rbp [REG]
	.globl main
	.type main, @function
main:
	pushq	%rbp
	# 0x400527:	movq	%rsp, %rbp [REG, REG]
	movq	%rsp, %rbp
	# 0x40052a:	subq	$0x10, %rsp [IMM, REG]
	subq	$0x10, %rsp
	# 0x40052e:	movl	$0x15, -4(%rbp) [IMM, MEM]
	movl	$0x15, -4(%rbp)
	# 0x400535:	movl	-4(%rbp), %eax [MEM, REG]
	movl	-4(%rbp), %eax
	# 0x400538:	movl	%eax, %esi [REG, REG]
	movl	%eax, %esi
	# 0x40053a:	movl	$0x4005d4, %edi [IMM <DATAREF>, REG]
	movl	$label_32,  %edi
	# 0x40053f:	movl	$0, %eax [IMM, REG]
	movl	$0, %eax
	# 0x400544:	callq	0x400400 [IMM <CODEREF>]
	callq	printf
	# 0x400549:	movl	-4(%rbp), %eax [MEM, REG]
	movl	-4(%rbp), %eax
	# 0x40054c:	addl	%eax, %eax [REG, REG]
	addl	%eax, %eax
	# 0x40054e:	leave	 []
	leave	
	# 0x40054f:	retq	 []
	retq	
	.section	.text
	.align	16
	#Procedure 0x400550

	# 0x400550:	pushq	%r15 [REG]
	.globl __libc_csu_init
	.type __libc_csu_init, @function
__libc_csu_init:
	pushq	%r15
	# 0x400552:	pushq	%r14 [REG]
	pushq	%r14
	# 0x400554:	movl	%edi, %r15d [REG, REG]
	movl	%edi, %r15d
	# 0x400557:	pushq	%r13 [REG]
	pushq	%r13
	# 0x400559:	pushq	%r12 [REG]
	pushq	%r12
	# 0x40055b:	leaq	0x2008ae(%rip), %r12 [MEM, REG]
	leaq	__init_array_start(%rip),  %r12
	# 0x400562:	pushq	%rbp [REG]
	pushq	%rbp
	# 0x400563:	leaq	0x2008ae(%rip), %rbp [MEM, REG]
	leaq	__init_array_end(%rip),  %rbp
	# 0x40056a:	pushq	%rbx [REG]
	pushq	%rbx
	# 0x40056b:	movq	%rsi, %r14 [REG, REG]
	movq	%rsi, %r14
	# 0x40056e:	movq	%rdx, %r13 [REG, REG]
	movq	%rdx, %r13
	# 0x400571:	subq	%r12, %rbp [REG, REG]
	subq	%r12, %rbp
	# 0x400574:	subq	$8, %rsp [IMM, REG]
	subq	$8, %rsp
	# 0x400578:	sarq	$3, %rbp [IMM, REG]
	sarq	$3, %rbp
	# 0x40057c:	callq	0x4003c8 [IMM <CODEREF>]
	callq	_init
	# 0x400581:	testq	%rbp, %rbp [REG, REG]
	testq	%rbp, %rbp
	# 0x400584:	je	0x4005a6 [IMM <CODEREF>]
	je	.label_33
	# 0x400586:	xorl	%ebx, %ebx [REG, REG]
	xorl	%ebx, %ebx
	# 0x400588:	nopl	(%rax, %rax) [MEM]
	nopl	(%rax, %rax)
	# 0x400590:	movq	%r13, %rdx [REG, REG]
.label_34:
	movq	%r13, %rdx
	# 0x400593:	movq	%r14, %rsi [REG, REG]
	movq	%r14, %rsi
	# 0x400596:	movl	%r15d, %edi [REG, REG]
	movl	%r15d, %edi
	# 0x400599:	callq	*(%r12, %rbx, 8) [MEM]
	callq	*(%r12, %rbx, 8)
	# 0x40059d:	addq	$1, %rbx [IMM, REG]
	addq	$1, %rbx
	# 0x4005a1:	cmpq	%rbp, %rbx [REG, REG]
	cmpq	%rbp, %rbx
	# 0x4005a4:	jne	0x400590 [IMM <CODEREF>]
	jne	.label_34
	# 0x4005a6:	addq	$8, %rsp [IMM, REG]
.label_33:
	addq	$8, %rsp
	# 0x4005aa:	popq	%rbx [REG]
	popq	%rbx
	# 0x4005ab:	popq	%rbp [REG]
	popq	%rbp
	# 0x4005ac:	popq	%r12 [REG]
	popq	%r12
	# 0x4005ae:	popq	%r13 [REG]
	popq	%r13
	# 0x4005b0:	popq	%r14 [REG]
	popq	%r14
	# 0x4005b2:	popq	%r15 [REG]
	popq	%r15
	# 0x4005b4:	retq	 []
	retq	
	.section	.text
	.align	16
	#Procedure 0x4005c0

	# 0x4005c0:	retq	 []
	.globl __libc_csu_fini
	.type __libc_csu_fini, @function
__libc_csu_fini:
	retq	
	.section	.fini
	.align	4
	#Procedure 0x4005c4

	# 0x4005c4:	subq	$8, %rsp [IMM, REG]
	.globl _fini
	.type _fini, @function
_fini:
	subq	$8, %rsp
	# 0x4005c8:	addq	$8, %rsp [IMM, REG]
	addq	$8, %rsp
	# 0x4005cc:	retq	 []
	retq	
	.section .plt.got
	.align 32
	# data @ 0x400428
	.label_44:
	.section .text
	.align 16
	# data @ 0x4005c2
	.label_45:
	.section .rodata
	.align 16
	# data @ 0x4005d0
	.byte 1
	.byte 0
	.byte 2
	.byte 0
label_32:
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
	.align 16
	# data @ 0x600e10
	.globl __init_array_start
	.type __init_array_start, @notype
__init_array_start:
	.quad frame_dummy
	.section .data
	.align 8
	# data @ 0x601028
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
	# data @ 0x601038
	.globl __TMC_END__
	.type __TMC_END__, @object
__TMC_END__:
	.byte 0x0
	# data @ 0x601039
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
	.byte 0
label_26:
	.byte 0
	# data @ 0x601040
		.globl _end
	.type _end, @notype
_end: