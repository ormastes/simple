# x86 Syscall Entry (int 0x80)
#
# This file provides the low-level assembly glue for system calls
# invoked via `int 0x80` from user mode.
#
# Calling convention (Linux-like):
#   eax = syscall number
#   ebx = arg0
#   ecx = arg1
#   edx = arg2
#   esi = arg3
#   edi = arg4
#
# Return value placed in eax.
#
# The actual vector 0x80 handler is registered via isr_stubs.S.
# This module provides the higher-level syscall dispatcher that
# isr_common calls through trap_handler -> handle_syscall.

.section .text
.code32

# ---------- Syscall dispatch entry ----------
#
# Called from trap_handler with a pointer to the TrapFrame on stack.
# We extract the syscall number from eax and arguments from ebx-edi,
# then call the Simple-language syscall_dispatch function.

.global syscall_entry
.align 16
syscall_entry:
    # On entry: [esp+4] = pointer to TrapFrame
    push %ebp
    mov %esp, %ebp

    # Load frame pointer
    mov 8(%ebp), %eax          # eax = &frame

    # Save callee-saved registers
    push %ebx
    push %esi
    push %edi

    # Extract syscall arguments from the saved frame
    # TrapFrame layout (from pusha):
    #   offset 0:  edi
    #   offset 4:  esi
    #   offset 8:  ebp
    #   offset 12: esp_dummy
    #   offset 16: ebx
    #   offset 20: edx
    #   offset 24: ecx
    #   offset 28: eax (syscall number)
    #   offset 32: vector
    #   offset 36: error_code
    #   offset 40: eip
    #   offset 44: cs

    mov %eax, %edi             # frame ptr in edi

    # Push arguments for syscall_dispatch(number, arg0, arg1, arg2, arg3, arg4)
    mov 0(%edi), %eax          # edi field = arg4
    push %eax
    mov 4(%edi), %eax          # esi field = arg3
    push %eax
    mov 20(%edi), %eax         # edx field = arg2
    push %eax
    mov 24(%edi), %eax         # ecx field = arg1
    push %eax
    mov 16(%edi), %eax         # ebx field = arg0
    push %eax
    mov 28(%edi), %eax         # eax field = syscall number
    push %eax

    # Call Simple-language dispatcher
    .extern syscall_dispatch
    call syscall_dispatch

    # Return value is in eax - store it back into the frame's eax slot
    mov %edi, %ecx
    mov %eax, 28(%ecx)        # frame.eax = return value

    # Clean up arguments
    add $24, %esp

    # Restore callee-saved registers
    pop %edi
    pop %esi
    pop %ebx

    pop %ebp
    ret

# ---------- User-space syscall wrapper ----------
#
# This would live in user-space libos, but we provide it here as reference.
# User code calls: syscall(number, arg0, arg1, arg2, arg3, arg4) -> i32
#
# Not assembled into the kernel; included for documentation.

#.section .text.user
#.global user_syscall
#.align 4
#user_syscall:
#    push %ebp
#    mov %esp, %ebp
#    push %ebx
#    push %esi
#    push %edi
#
#    mov  8(%ebp), %eax        # syscall number
#    mov 12(%ebp), %ebx        # arg0
#    mov 16(%ebp), %ecx        # arg1
#    mov 20(%ebp), %edx        # arg2
#    mov 24(%ebp), %esi        # arg3
#    mov 28(%ebp), %edi        # arg4
#
#    int $0x80
#
#    pop %edi
#    pop %esi
#    pop %ebx
#    pop %ebp
#    ret
