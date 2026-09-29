# RV32 real filesystem execution live closure

Status: source-corrected, live verification deferred by three-cycle cap.

The fresh RV32 transcript initially failed before listing because the fixed
118-byte `QEMUNONC.TXT` slot is newline-terminated and then NUL-padded. The
reader incorrectly required byte 117 itself to be newline. The bounded reader
now identifies one valid line and requires zero-only trailing padding. QEMU
cycle 1 proved the exact target-read nonce and ten real `/SYS/APPS` dirents.

RV32 now loads the mounted root `/FSEXEC.ELF` PT_LOAD records into a private
arena, enters their actual instructions in U-mode, services only stdout ecall
60 and exit ecall 0 from an M-mode trap owner, resumes at a saved supervisor
PC, validates exit 37, and emits the reap receipt. Cycle 2 found assembly-only
handoff storage removed by section GC; explicit retained symbols fixed it.
Cycle 3 stopped before entry because the loader's FAT key had one space where
the canonical 8.3 name has two (`FSEXEC  ELF`). That key is corrected.

No PASS is claimed. Cycles 2/3 also used the wrapper's default compiler SHA
`2ec710...`, because the correct override is `SIMPLEOS_REBUILD_COMPILER`.
A fresh session must perform one rebuild with admitted compiler SHA
`a3b935...`, patch a fresh nonce clone, and require the full marker sequence:
boot, exact nonce, live listing, `FS_PROGRAM_BEGIN`, target-produced nonce
stdout, `FS_PROGRAM_END rc=37 reaped=true`, and `TEST PASSED`.

## Admitted-compiler verification

The fresh rebuild used the correct `SIMPLEOS_REBUILD_COMPILER` override and its
receipt records compiler SHA `a3b9354c...` and kernel SHA `fe801bbb...`. One TCG
boot reached the real mounted entry and printed the exact nonce-bearing stdout
from the child, then timed out. It did not emit exit 37, recovery/reap, or final
PASS. Evidence is retained under
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/rv32-live-authority-20260812/`.

The next source repair should set `mstatus.MPP` to M on the exit and fault
branches before `mret` redirects to the supervisor recovery PC. The current
trap retains MPP=U from the child trap, so the redirected recovery executes at
U privilege and traps on its first CSR instruction. This diagnosis is a static
inference from the exact stop point and trap sequence; it is not yet a live
PASS.

MPP=M restoration was implemented on exit and fault paths, with a focused
sabotage/assembled-instruction gate at
`scripts/check/check-rv32-real-fs-exec-trap.shs`. The one admitted-compiler
rebuild produced kernel SHA `cfefb6e5...`; its one TCG run still stopped after
the exact target stdout. Exit/reap/PASS remain absent.

The next bounded repair must make the C inline-assembly boundary honest about
the non-ABI child excursion. The child modifies `a0`, `a7`, `s1`, and `s2`, but
the current transition declares only `t0`, `t1`, and memory as clobbered. This
permits the compiler to retain continuation state or the saved `mtvec` output
in registers destroyed by the child. Add the complete clobber contract (or use
an assembly owner with an explicit saved frame), then rebuild/run in a fresh
bounded cycle. Evidence is retained at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/rv32-mpp-recovery-20260812/`.

## Functional closure

The transition now declares `a0`, `a7`, `s1`, and `s2` alongside its existing
temporary and memory clobbers. The focused gate confirms source ownership and
emitted LLVM clobber metadata, including sabotage that removes one required
register.

One admitted-LLVM rebuild produced kernel SHA `21faf5e2...`. One TCG boot
exited zero and contains the exact target nonce, ten real `/SYS/APPS` entries,
mounted ELF readback SHA `63f7726c...`, target-originated stdout, exit 37,
supervisor recovery/exact-child reap, and final `TEST PASSED`. Evidence is at
`/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/rv32-clobber-ownership-20260812/`.
The result is a functional diagnostic PASS, not a collector promotion: the
shared worktree does not provide a clean immutable source identity.
