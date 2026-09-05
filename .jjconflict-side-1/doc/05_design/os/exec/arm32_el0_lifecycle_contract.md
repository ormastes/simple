# ARM32 EL0 filesystem-exec lifecycle contract

Status: blocked by implementation. The gate validates the rejection boundary;
it is not QEMU evidence.

`arm32-virtio-fat32-smf` currently exercises NVFS/SMF capability probes. Its
`TEST PASSED` output is insufficient: it does not prove a mounted
`/FSEXEC.ELF` runs at EL0, returns through SVC, and is reaped by the kernel.

`scripts/check/check-arm32-user-lifecycle-contract.shs --contract` proves
that this probe transcript lacks the canonical filesystem-exec markers. Matrix
execution invokes `--admit`; until all owners below are present it fails before
QEMU and cannot publish an ARM32 native bundle.

Admission requires:

1. `examples/09_embedded/simple_os/arch/arm32/boot/enter_user_first.s` owns
   `rt_arm32_enter_user_first`, installs an EL0 return frame (SPSR + user SP),
   and performs `movs` exception return.
2. `exception_vectors.s` owns `rt_arm32_svc_vector`; the freestanding runtime
   initializes that vector and owns `rt_arm32_svc_resume_kernel` to restore the
   authenticated kernel continuation after user exit.
3. `src/os/kernel/arch/arm32/user_entry.spl` installs and consumes a one-shot
   token through `rt_arm32_exec_token_install` and
   `rt_arm32_exec_token_take_result`. It binds task identity, generation, and
   address-space root.
4. `fs_exec_entry.spl` reads the mounted program through
   `rt_arm32_fs_read_program`, enters through `rt_arm32_enter_user_first`, and
   emits the descriptor's list/program/reap markers only from that lifecycle.
5. ARM32 context restore must load its destination; a no-op restore cannot
   qualify as scheduler or trap return support.
6. A new clean QEMU transcript must show boot, real `/SYS/APPS` listing,
   mounted `/FSEXEC.ELF` EL0 nonce, exit `37`/reap, and `TEST PASSED` in order.

Run `--self-test` for the current fail-closed boundary. `--admit` is reserved
for matrix execution; its failure is an implementation blocker, not a skipped
test.
