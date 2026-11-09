.text
.p2align 4
.globl security_return_control
.def security_return_control; .scl 2; .type 32; .endef
security_return_control:
    hint #34 // BTI c; presence is not evidence of BTI enforcement.
    hint #27 // PACIBSP
    mov w0, #0x5678
    hint #31 // AUTIBSP with the same SP: positive authentication control.
    ret

.p2align 4
.globl security_pac_sign_active
.def security_pac_sign_active; .scl 2; .type 32; .endef
security_pac_sign_active:
    hint #34
    mov x9, x30
    hint #27
    cmp x30, x9
    cset w0, ne
    hint #31
    ret

.p2align 4
.globl security_pac_bad_return
.def security_pac_bad_return; .scl 2; .type 32; .endef
security_pac_bad_return:
    hint #34
    hint #27 // Sign the valid incoming LR with the original SP.
    sub sp, sp, #16
    hint #31 // Wrong SP modifier: poison LR or a synchronous PAC fault.
    add sp, sp, #16
    // With PAC instructions behaving as hints this returns normally and the
    // child exits with sentinel 78. With PAC enforcing, poisoned LR must fault.
    ret
