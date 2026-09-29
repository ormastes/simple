/* ARMv7-A v1.4 vector, first User entry, and SVC frame consumer. */
    .syntax unified
    .arm
    .section .vectors.arm32.v12,"ax",%progbits
    .align 5
    .global arm32_vector_table_v12
arm32_vector_table_v12:
    ldr pc, 1f
    ldr pc, 2f
    ldr pc, 3f
    ldr pc, 4f
    ldr pc, 5f
    ldr pc, 6f
    ldr pc, 7f
    ldr pc, 8f
1:  .word arm32_vector_reject_v14
2:  .word arm32_vector_reject_v14
3:  .word arm32_svc_entry_v14
4:  .word arm32_vector_reject_v14
5:  .word arm32_vector_reject_v14
6:  .word arm32_vector_reject_v14
7:  .word arm32_vector_reject_v14
8:  .word arm32_vector_reject_v14

    .text
    .align 2
    .global arm32_vector_install_v1
arm32_vector_install_v1:
    tst r0, #31
    bne arm32_vector_reject_v14
    mcr p15, 0, r0, c12, c0, 0
    dsb sy
    isb
    bx lr

    .global arm32_enter_user_v1
arm32_enter_user_v1:
    /* r0=token, r1=entry, r2=user SP. Token was parent-issued/authenticated. */
    push {r4-r8,lr}
    mov r4,r0
    mov r5,r1
    mov r6,r2
    bl arm32_platform_cpu_id_v12
    mov r7,r0
    bl arm32_token_lookup_active_v11
    cmp r0,r4
    bne arm32_enter_fail_v14
    mov r0,r7
    mov r1,#1
    mov r2,#2
    bl arm32_token_advance_v11
    cmp r0,#1
    bne arm32_enter_fail_v14
    ldr r8,[r4,#20]             /* user_ttbr0_root */
    ldr r3,[r4,#32]             /* supervisor_sp */
    mcr p15,0,r8,c2,c0,0
    dsb sy
    mov r0,#0
    mcr p15,0,r0,c8,c7,0
    dsb sy
    isb
    cps #0x1f                   /* System mode shares User SP/LR */
    mov sp,r6
    mov lr,#0
    cps #0x13
    mov sp,r3                   /* dedicated SVC stack top */
    mov r0,#0x10
    msr spsr_cxsf,r0
    mov lr,r5
    movs pc,lr
arm32_enter_fail_v14:
    mov r0,#0
    pop {r4-r8,pc}

    .global arm32_svc_entry_v14
arm32_svc_entry_v14:
    cpsid if
    sub sp,sp,#72
    stmia sp,{r0-r12}
    add r0,sp,#52
    stmia r0,{sp,lr}^
    nop
    sub r1,lr,#4
    str r1,[sp,#60]
    mrs r2,spsr
    str r2,[sp,#64]
    ldr r3,[r1]
    str r3,[sp,#68]
    sub sp,sp,#64               /* bounded disposition storage */
    bl arm32_platform_cpu_id_v12
    mov r4,r0
    add r1,sp,#64               /* immutable frame */
    mrc p15,0,r2,c2,c0,0
    bic r2,r2,#0x3f
    bic r2,r2,#0x3fc0
    mov r3,sp
    mov r0,r4
    bl arm32_svc_dispatch_disposition_v14
    cmp r0,#1
    bne arm32_svc_reject_v14
    mov r0,r4
    mov r1,sp
    bl arm32_scheduler_commit_disposition_v14
    cmp r0,#1
    beq arm32_svc_return_user_v14
    cmp r0,#2
    beq arm32_svc_resume_parent_v14
arm32_svc_reject_v14:
    add sp,sp,#136
arm32_vector_reject_v14:
    cpsid if
9:  wfe
    b 9b

arm32_svc_return_user_v14:
    add sp,sp,#64
    ldr r1,[sp,#64]
    msr spsr_cxsf,r1
    add r0,sp,#52
    ldmia r0,{sp,lr}^
    nop
    ldr lr,[sp,#60]
    ldmia sp,{r0-r12}
    add sp,sp,#72
    movs pc,lr

arm32_svc_resume_parent_v14:
    mov r0,r4
    bl arm32_token_lookup_active_v11
    cmp r0,#0
    beq arm32_svc_reject_v14
    ldr r1,[r0,#40]             /* kernel_ttbr0_root */
    ldr r2,[r0,#32]             /* supervisor_sp */
    ldr r3,[r0,#36]             /* supervisor_pc */
    mcr p15,0,r1,c2,c0,0
    dsb sy
    mov r1,#0
    mcr p15,0,r1,c8,c7,0
    dsb sy
    isb
    mov sp,r2
    bx r3
