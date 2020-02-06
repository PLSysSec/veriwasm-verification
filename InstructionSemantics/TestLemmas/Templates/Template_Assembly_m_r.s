	.intel_syntax noprefix

	.section .data
	.align 16
MemOperand:	
	.byte %4%
	.byte %5%
	.byte %6%
	.byte %7%
	.byte %8%
	.byte %9%
	.byte %10%
	.byte %11%

	.section	.text
	.align	16
	.globl main
	.type main, @function
main:
	%1% %2% [MemOperand] %3%
	ret
		
		