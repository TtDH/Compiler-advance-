IO:
	.string "%lld"
	.text
	.globl main
main:
	pushq %rbp
	movq %rsp, %rbp
	subq $16, %rsp
	pushq $2
	pushq $5
	popq %rbx
	popq %rax
	pushq %rbx
	popq %rcx
	movq $1, %rdx
L1:
	cmpq $0, %rcx
	je L2
	imulq %rax, %rdx
	subq $1, %rcx
	jmp L1
L2:
	pushq %rdx
	movq %rbp, %rax
	leaq -8(%rax), %rax
	popq (%rax)
	movq %rbp, %rax
	leaq -8(%rax), %rax
	movq (%rax), %rax
	pushq %rax
	popq  %rsi
	leaq IO(%rip), %rdi
	movq $0, %rax
	callq printf
	leaveq
	retq
