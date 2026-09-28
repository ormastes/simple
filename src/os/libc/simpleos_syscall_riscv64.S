/* SimpleOS RV64 user syscall and architecture-neutral guest-mode shim. */
.section .text
.global simpleos_syscall
.type simpleos_syscall, @function
simpleos_syscall:
    mv a7, a0
    mv a0, a1
    mv a1, a2
    mv a2, a3
    mv a3, a4
    mv a4, a5
    ecall
    ret
.size simpleos_syscall, . - simpleos_syscall

.global simpleos_guest_arch_id
.type simpleos_guest_arch_id, @function
simpleos_guest_arch_id:
    li a0, 3
    ret
.size simpleos_guest_arch_id, . - simpleos_guest_arch_id

.global simpleos_user_context_ok
.type simpleos_user_context_ok, @function
simpleos_user_context_ok:
    li a7, 4
    ecall
    slt a0, zero, a0
    ret
.size simpleos_user_context_ok, . - simpleos_user_context_ok

.global simpleos_current_cs
.type simpleos_current_cs, @function
simpleos_current_cs:
    li a0, 0x2b
    ret
.size simpleos_current_cs, . - simpleos_current_cs

.global __clear_cache
.type __clear_cache, @function
__clear_cache:
    fence.i
    ret
.size __clear_cache, . - __clear_cache
