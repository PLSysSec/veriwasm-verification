    .intel_syntax noprefix

    .section    .text
    .align    32
    .globl main
    .type main, @function
main:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    push    rbx # Size:1, Opcode: 0x53,0x00,0x00,0x00
    sub    rsp, 0x58 # Size:4, Opcode: 0x83,0x00,0x00,0x00
    mov    rax, qword ptr fs:[0x28] # Size:9, Opcode: 0x8b,0x00,0x00,0x00
    mov    qword ptr [rbp - 0x18], rax # Size:4, Opcode: 0x89,0x00,0x00,0x00
    xor    eax, eax # Size:2, Opcode: 0x31,0x00,0x00,0x00
    lea    rax, qword ptr [rbp - 0x50] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
    mov    rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    _ZN5StackIiEC2Ev # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    mov    dword ptr [rbp - 0x5c], 7 # Size:7, Opcode: 0xc7,0x00,0x00,0x00
    lea    rdx, qword ptr [rbp - 0x5c] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
    lea    rax, qword ptr [rbp - 0x50] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
    mov    rsi, rdx # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    _ZN5StackIiE4pushERKi # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    lea    rax, qword ptr [rbp - 0x50] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
    mov    rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    _ZNK5StackIiE3topEv # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    mov    esi, eax # Size:2, Opcode: 0x89,0x00,0x00,0x00
    lea    rdi,  qword ptr [word ptr [rip + __bss_start]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
    call    _ZNSolsEi # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    mov    rdx, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    rax,  qword ptr [word ptr [rip + label_10]] # Size:7, Opcode: 0x8b,0x00,0x00,0x00
    mov    rsi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    rdi, rdx # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    _ZNSolsEPFRSoS_E # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    lea    rax, qword ptr [rbp - 0x50] # Size:4, Opcode: 0x8d,0x00,0x00,0x00
    mov    rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    _ZN5StackIiE3popEv # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    mov    ebx, 0 # Size:5, Opcode: 0xbb,0x00,0x00,0x00
    mov    eax, ebx # Size:2, Opcode: 0x89,0x00,0x00,0x00
    mov    rcx, qword ptr [rbp - 0x18] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    xor    rcx, qword ptr fs:[0x28] # Size:9, Opcode: 0x33,0x00,0x00,0x00
    je    .label_11 # Size:6, Opcode: 0x0f,0x84,0x00,0x00
    jmp    .label_12 # Size:5, Opcode: 0xe9,0x00,0x00,0x00
.label_12:
    call    __stack_chk_fail # Size:5, Opcode: 0xe8,0x00,0x00,0x00
.label_11:
    add    rsp, 0x58 # Size:4, Opcode: 0x83,0x00,0x00,0x00
    pop    rbx # Size:1, Opcode: 0x5b,0x00,0x00,0x00
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _Z41__static_initialization_and_destruction_0ii
    .type _Z41__static_initialization_and_destruction_0ii, @function
_Z41__static_initialization_and_destruction_0ii:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    sub    rsp, 0x10 # Size:4, Opcode: 0x83,0x00,0x00,0x00
    mov    dword ptr [rbp - 4], edi # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    dword ptr [rbp - 8], esi # Size:3, Opcode: 0x89,0x00,0x00,0x00
    cmp    dword ptr [rbp - 4], 1 # Size:4, Opcode: 0x83,0x00,0x00,0x00
    jne    .label_14 # Size:2, Opcode: 0x75,0x00,0x00,0x00
    cmp    dword ptr [rbp - 8], 0xffff # Size:7, Opcode: 0x81,0x00,0x00,0x00
    jne    .label_14 # Size:2, Opcode: 0x75,0x00,0x00,0x00
    lea    rdi,  qword ptr [word ptr [rip + _ZStL8__ioinit]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
    call    _ZNSt8ios_base4InitC1Ev # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    lea    rdx,  qword ptr [word ptr [rip + __dso_handle]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
    lea    rsi,  qword ptr [word ptr [rip + _ZStL8__ioinit]] # Size:7, Opcode: 0x8d,0x00,0x00,0x00
    mov    rax,  qword ptr [word ptr [rip + label_13]] # Size:7, Opcode: 0x8b,0x00,0x00,0x00
    mov    rdi, rax # Size:3, Opcode: 0x89,0x00,0x00,0x00
    call    __cxa_atexit # Size:5, Opcode: 0xe8,0x00,0x00,0x00
.label_14:
    nop     # Size:1, Opcode: 0x90,0x00,0x00,0x00
    leave     # Size:1, Opcode: 0xc9,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _GLOBAL__sub_I_main
    .type _GLOBAL__sub_I_main, @function
_GLOBAL__sub_I_main:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    esi, 0xffff # Size:5, Opcode: 0xbe,0x00,0x00,0x00
    mov    edi, 1 # Size:5, Opcode: 0xbf,0x00,0x00,0x00
    call    _Z41__static_initialization_and_destruction_0ii # Size:5, Opcode: 0xe8,0x00,0x00,0x00
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _ZN5StackIiEC2Ev
    .type _ZN5StackIiEC2Ev, @function
_ZN5StackIiEC2Ev:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    qword ptr [rbp - 8], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    mov    word ptr [rax + 0x28], 0 # Size:6, Opcode: 0xc7,0x00,0x00,0x00
    nop     # Size:1, Opcode: 0x90,0x00,0x00,0x00
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _ZN5StackIiE4pushERKi
    .type _ZN5StackIiE4pushERKi, @function
_ZN5StackIiE4pushERKi:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    qword ptr [rbp - 8], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
    mov    qword ptr [rbp - 0x10], rsi # Size:4, Opcode: 0x89,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    movzx    edx, ax # Size:3, Opcode: 0x0f,0xb7,0x00,0x00
    mov    rax, qword ptr [rbp - 0x10] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    mov    ecx, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movsxd    rdx, edx # Size:3, Opcode: 0x63,0x00,0x00,0x00
    mov    dword ptr [rax + rdx*4], ecx # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    lea    edx, dword ptr [rax + 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    mov    word ptr [rax + 0x28], dx # Size:4, Opcode: 0x89,0x00,0x00,0x00
    nop     # Size:1, Opcode: 0x90,0x00,0x00,0x00
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _ZNK5StackIiE3topEv
    .type _ZNK5StackIiE3topEv, @function
_ZNK5StackIiE3topEv:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    qword ptr [rbp - 8], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    test    ax, ax # Size:3, Opcode: 0x85,0x00,0x00,0x00
    je    .label_15 # Size:2, Opcode: 0x74,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    movzx    eax, ax # Size:3, Opcode: 0x0f,0xb7,0x00,0x00
    lea    edx, dword ptr [rax - 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movsxd    rdx, edx # Size:3, Opcode: 0x63,0x00,0x00,0x00
    mov    eax, dword ptr [rax + rdx*4] # Size:3, Opcode: 0x8b,0x00,0x00,0x00
    jmp    .label_16 # Size:2, Opcode: 0xeb,0x00,0x00,0x00
.label_15:
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    mov    eax, dword ptr [rax] # Size:2, Opcode: 0x8b,0x00,0x00,0x00
.label_16:
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00

    .section    .text
    .align    32
    .globl _ZN5StackIiE3popEv
    .type _ZN5StackIiE3popEv, @function
_ZN5StackIiE3popEv:
    push    rbp # Size:1, Opcode: 0x55,0x00,0x00,0x00
    mov    rbp, rsp # Size:3, Opcode: 0x89,0x00,0x00,0x00
    mov    qword ptr [rbp - 8], rdi # Size:4, Opcode: 0x89,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    test    ax, ax # Size:3, Opcode: 0x85,0x00,0x00,0x00
    je    .label_17 # Size:2, Opcode: 0x74,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    movzx    eax, word ptr [rax + 0x28] # Size:4, Opcode: 0x0f,0xb7,0x00,0x00
    lea    edx, dword ptr [rax - 1] # Size:3, Opcode: 0x8d,0x00,0x00,0x00
    mov    rax, qword ptr [rbp - 8] # Size:4, Opcode: 0x8b,0x00,0x00,0x00
    mov    word ptr [rax + 0x28], dx # Size:4, Opcode: 0x89,0x00,0x00,0x00
.label_17:
    nop     # Size:1, Opcode: 0x90,0x00,0x00,0x00
    pop    rbp # Size:1, Opcode: 0x5d,0x00,0x00,0x00
    ret     # Size:1, Opcode: 0xc3,0x00,0x00,0x00


    .section .comment
    .align 32
label_20:
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
    .byte 128
    .byte 10
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

    .section .symtab
    .align 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 160
    .byte 46
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
    .byte 30
    .byte 0
    .byte 29
    .byte 0
    .byte 6
    .byte 0
    .byte 0
    .byte 0
    .byte 4
    .byte 0
    .quad label_20
    .quad label_20
    .quad label_20
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
    .byte 224
    .byte 16
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 224
    .byte 16
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
    .byte 64
    .byte 29
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 64
    .byte 29
    .byte 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 64
    .byte 29
    .byte 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 224
    .byte 2
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 24
    .byte 5
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
    .byte 88
    .byte 29
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 88
    .byte 29
    .byte 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 88
    .byte 29
    .byte 32
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
    .byte 100
    .byte 14
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 100
    .byte 14
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 100
    .byte 14
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
    .byte 64
    .byte 29
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 64
    .byte 29
    .byte 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 64
    .byte 29
    .byte 32
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 192
    .byte 2
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 192
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
    label_26:

    .section .symtab
    .align 32
    label_25:

    .section .rodata
    .align 16
    .byte 1
    .byte 0
    .byte 2
    .byte 0
    .byte 0
    .byte 69
    .byte 120
    .byte 99
    .byte 101
    .byte 112
    .byte 116
    .byte 105
    .byte 111
    .byte 110
    .byte 58
    .byte 32
    .byte 0
    .label_23:

    .section .gcc_except_table
    .align 32
    .byte 255
    .byte 155
    .byte 29
    .byte 1
    .byte 21
    .byte 83
    .byte 26
    .byte 152
    .byte 1
    .byte 1
    .byte 161
    .byte 1
    .byte 5
    .byte 0
    .byte 0
    .byte 192
    .byte 1
    .byte 63
    .byte 142
    .byte 2
    .byte 0
    .byte 156
    .byte 2
    .byte 5
    .byte 0
    .byte 0
    .byte 1
    .byte 0
    .byte 52
    .byte 15
    .byte 32
    .byte 0
    .label_24:

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
    .byte 24
    .byte 0
    .byte 0
    .byte 1
    .byte 0
    .byte 0
    .byte 0
    .byte 0
    .byte 32
    .byte 0
    .byte 0
    .byte 1
    .byte 0
    .byte 0
    .byte 0
    .byte 0

    .section .bss
    .align 32
    .globl __bss_start
    .type __bss_start, @notype
__bss_start:
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
    .byte 0
    .globl completed.7696
    .type completed.7696, @object
completed.7696:
    .byte 0x0
    .globl _ZStL8__ioinit
    .type _ZStL8__ioinit, @object
_ZStL8__ioinit:
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
