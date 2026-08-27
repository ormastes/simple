<!-- codex-design -->
# x86_32 privilege-transition ABI detail design

The packed trap frame is 76 bytes. Assembly saves `GS, FS, ES, DS`, then
`pushal`, then vector and synthetic error, followed by the CPU's CPL3 frame:
`EIP, CS, EFLAGS, user ESP, user SS`. Offsets are frozen in
`privilege_abi.spl`; same-CPL frames are invalid for this entry.

The packed 96-byte token has states empty, armed, exiting, and consumed. Arming
requires a scheduled user TCB, matching private CR3, nonzero generation and
address-space ID, allocated kernel stack, bounded nonce, and saved kernel
continuation. State publication is the final release operation. Trap dispatch
loads one snapshot and revalidates current scheduler identity and CR3 before
any effect.

ABI v1.1 freezes this raw-C prototype:

```text
i32 simpleos_x86_32_privilege_dispatch_v1_1(
    const frame*, token*, u32 observed_cr3, disposition_out*)
```

It uses cdecl with four 32-bit stack arguments and returns a scalar i32. All
three pointers are non-null and four-byte aligned. Zero means the complete
16-byte output was initialized; negative errno rejects and requires the caller
to ignore every output byte. The symbol is strong and unique. Aggregate return,
`RuntimeValue`, weak declarations, aliasing, and fallback symbol probing are
forbidden.

For return-user, assembly writes disposition `eax`, restores the frame, and
`iret`s. For resume-kernel-exit, assembly switches to kernel CR3, loads the
saved kernel ESP, and jumps to the saved EIP. Reject terminates the offending
task through a non-returning kernel fault path; it never guesses a stack.

Required sabotage cases: altered CS/SS, same-CPL short frame, wrong TaskId,
stale generation, changed CR3/address-space ID, nonce substitution, invalid
user range, syscall other than 60/0, exit other than 37, replayed exit, and
destroy-before-reap.

ABI v1.2 first entry is the strong cdecl noreturn function
`simpleos_x86_32_privilege_enter_v1_2(token*, kernel_stack_top, eip, user_esp,
user_cr3)`. Validation precedes all mutation. Occupied CPU-local slot returns
through a separate preparation error before this noreturn call. The architecture
sets `TSS.esp0`, release-publishes the token, switches CR3, and enters user mode.
The compare-clear function consumes only the identical token pointer.

The token pointer is backed by the architecture-common fixed packed storage,
not a Simple array element. A scheduler claim reserves exactly one 96-byte
aligned record under a nonzero generation lease, serializes every token byte,
and publishes the address only after identity validation. Revoke validates the
same lease and volatile-wipes the record before reuse. This closes storage
stability but does not itself install GDT/TSS or the CPL3 trap boundary.

Scheduler preparation allocates four contiguous identity-accessible pages,
records their base/top/count on the same TCB, and creates the token from that
TCB's TaskId, capability generation, address-space ID, and CR3. Failure before
publication frees immediately. Once published, only the trap/fault owner may
clear it. Reap ordering is fixed: clear, exit exact child, collect exact child,
free kernel stack, destroy user page directory.

ABI v1.3 adds `expected_nonce_user_va` at token offset 56, moves nonce length
to 60 and digest to 64, and makes the token 96 bytes. The admitted nonce is a
nonempty range of at most 4096 bytes with `va < 0xC0000000` and
`length <= 0xC0000000 - va`; subtraction form prevents addition overflow.
Every covered PTE must be present and user-readable but not writable. Entry
loads ECX=VA and EDX=length. The payload then supplies EBX/ECX to syscall 60;
both must equal the token exactly before the range is read or hashed.

ABI v1.4 preparation order is: reject PT_LOAD overlap at `0x2FFFF000`; claim a
generation-bearing registry slot; allocate kernel stack and nonce frame; zero
the frame; copy exact admitted bytes; compute and compare digest; map the page
read-only at the reserved VA; fill and pin the kernel token; return the frozen
preparation result to entry. Rollback reverses only completed steps. Normal
completion is compare-clear active token, validate encoded exit disposition,
mark/collect exact child, unmap/free nonce, revoke registry lease, free kernel
stack, then destroy the address space. Stale lease generations cannot revoke a
reused slot.
