	.intel_syntax noprefix

		.section .data
	.align 64
MemOperand:	
	.byte %2%
	.byte %3%
	.byte %4%
	.byte %5%
	.byte %6%
	.byte %7%
	.byte %8%
	.byte %9%
	.byte %10%
	.byte %11%
	.byte %12%
	.byte %13%
	.byte %14%
	.byte %15%
	.byte %16%
	.byte %17%
	.byte %18%
	.byte %19%
	.byte %20%
	.byte %21%
	.byte %22%
	.byte %23%
	.byte %24%
	.byte %25%
	.byte %26%
	.byte %27%
	.byte %28%
	.byte %29%
	.byte %30%
	.byte %31%
	.byte %32%
	.byte %33%

	.section	.text
	.align	64
	.globl main
	.type main, @function
main:
	%1% [MemOperand]
	ret
		
		