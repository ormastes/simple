# x86 Context Switch
#
# Saves the current thread's callee-saved registers and stack pointer,
# then restores the new thread's registers and resumes execution.
#
# Prototype (called from Simple):
#   context_switch(old_regs_ptr: u32, new_regs_ptr: u32)
#
# old_regs_ptr: pointer to storage where current ESP will be saved
# new_regs_ptr: pointer to storage containing the new ESP to load
#
# The callee-saved registers (ebx, esi, edi, ebp) are pushed onto the
# current stack before saving ESP, and popped from the new stack after
# loading it.  The return address on the new stack causes `ret` to
# jump to the new thread's continuation point.

.section .text
.code32

.global context_switch
.align 16
context_switch:
    # ---------- Save current context ----------

    # Arguments:
    #   [esp+4] = old_regs_ptr (where to save current ESP)
    #   [esp+8] = new_regs_ptr (where to load new ESP from)

    # Save callee-saved registers on the current stack
    push %ebp
    push %ebx
    push %esi
    push %edi

    # Save EFLAGS
    pushf

    # Save current ESP into *old_regs_ptr
    mov 24(%esp), %eax         # old_regs_ptr (adjusted for 5 pushes)
    mov %esp, (%eax)

    # ---------- Load new context ----------

    # Load new ESP from *new_regs_ptr
    mov 28(%esp), %eax         # new_regs_ptr (adjusted for 5 pushes)
    mov (%eax), %esp

    # Restore EFLAGS
    popf

    # Restore callee-saved registers from the new stack
    pop %edi
    pop %esi
    pop %ebx
    pop %ebp

    # `ret` pops the return address from the new stack,
    # resuming the new thread where it left off (or at its entry point)
    ret

# ---------- Initial context setup helper ----------
#
# Prepares a new thread's kernel stack so that the first context_switch
# into it will start executing at the given entry point.
#
# Prototype:
#   context_setup_stack(stack_top: u32, entry_point: u32) -> u32
#
# Returns the initial ESP value to store in the thread's saved-state.
# The stack is laid out so that context_switch's restore sequence
# (popf, pop edi/esi/ebx/ebp, ret) works correctly.

.global context_setup_stack
.align 16
context_setup_stack:
    push %ebp
    mov %esp, %ebp

    mov 8(%ebp), %eax         # stack_top
    mov 12(%ebp), %ecx        # entry_point

    # Build the initial stack frame (grows downward):
    #   [top - 4]  = entry_point   (consumed by `ret`)
    #   [top - 8]  = 0             (initial ebp)
    #   [top - 12] = 0             (initial ebx)
    #   [top - 16] = 0             (initial esi)
    #   [top - 20] = 0             (initial edi)
    #   [top - 24] = 0x0202        (initial EFLAGS: IF set, reserved bit 1)

    sub $4, %eax
    mov %ecx, (%eax)          # return address = entry_point

    sub $4, %eax
    movl $0, (%eax)            # ebp = 0

    sub $4, %eax
    movl $0, (%eax)            # ebx = 0

    sub $4, %eax
    movl $0, (%eax)            # esi = 0

    sub $4, %eax
    movl $0, (%eax)            # edi = 0

    sub $4, %eax
    movl $0x0202, (%eax)       # EFLAGS (IF=1, reserved bit 1)

    # eax now points to the initial ESP value
    pop %ebp
    ret

# ---------- Thread exit trampoline ----------
#
# If a kernel thread's entry function returns, execution falls through
# to here.  We halt rather than executing garbage.

.global context_thread_exit
.align 4
context_thread_exit:
    cli
.Lhalt_loop:
    hlt
    jmp .Lhalt_loop
