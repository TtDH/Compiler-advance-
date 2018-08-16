IO:
    .string "answer:%d\n"
    .text
    .global main
main:
    pushq %rbp
    movq %rsp, %rbp
    movq $10, %rax
    movq (%rax), %rbx
    leaq IO(%rip), %rdi
    movq %rax, %rsi
    movq $0, %rax
    callq printf
    leaveq
    retq
