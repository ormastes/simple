# x86_32 CPL3 filesystem-exec lifecycle contract

Status: blocked by implementation; the contract gate is green only for the
rejection boundary.  It is not live-QEMU evidence.

The existing `x86_32-initrd-fat32-smf` entry reads a Multiboot module and
searches bytes for fixture names.  Its `int 0x80` is invoked from CPL0.  It
cannot satisfy the QEMU matrix requirement for a mounted filesystem program
at CPL3, even if it prints `TEST PASSED`.

`scripts/check/check-x86-32-cpl3-lifecycle-contract.shs --contract` makes the
descriptor reject that legacy transcript.  Matrix execution calls `--admit`;
until every item below is real, it fails before QEMU and cannot publish a
native pass bundle.

Admission requires these owners and interfaces:

1. `examples/09_embedded/simple_os/arch/x86_32/boot/enter_user_first.s` owns
   `rt_x86_32_enter_user_first` and performs the i386 `iret` CPL transition.
2. The x86_32 freestanding stub owns `rt_x86_32_tss_init` and
   `rt_x86_32_tss_set_esp0`, with a loaded TSS and kernel trap stack before
   user entry.
3. `src/os/kernel/arch/x86_32/user_entry.spl` authenticates the handoff with
   `rt_x86_32_exec_token_install` and `rt_x86_32_exec_token_take_result`.
   The token binds task identity, generation, and address-space root; it is
   consumed once on exit/reap.
4. The x86_32 context implementation restores its destination rather than
   discarding `to`; a context or trap return cannot silently remain in the
   bootstrap task.
5. A fresh QEMU run emits the descriptor markers in order: boot, real
   `/SYS/APPS` list, mounted `/FSEXEC.ELF` CPL3 nonce, exit 37/reap, and
   `TEST PASSED`.  Only then may the native producer create row evidence.

Run `--self-test` for the current fail-closed boundary.  Run `--admit` only
from a row runner; a failure is an implementation blocker, not a skipped test.
