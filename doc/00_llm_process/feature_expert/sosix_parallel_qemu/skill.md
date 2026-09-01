# SOSIX Parallel QEMU Feature Expert

Canonical artifacts are the selected requirements, architecture, and design
named `sosix_parallel_qemu_refactor.md`; the agent plan under
`doc/03_plan/agent_tasks/`; and
`doc/07_guide/platform/simpleos/qemu_system_tests.md`. Execution belongs to
`scripts/check/check-sosix-qemu-matrix.shs`. Construction-only work uses
`scripts/check/rebuild-sosix-qemu-media.shs`; nonce clones use
`scripts/os/prepare_qemu_nonce_media.shs`.

PASS requires clean source, admitted pure-Simple compiler, firmware/QEMU
hashes, executed accelerator, target-read nonce, boot/mount, live target-side
`/SYS/APPS` dirent listing, and arbitrary filesystem-program stdout with rc=0.
Compiler-bearing rows also prove target-native version and compile/run.

Current release admission on 2026-08-12 is **0 PASS / 24**. Linux x86_32,
ARM32, RISC-V32, and RISC-V64 diagnostic transcripts prove capability but are
not collector PASS. x86_64 image capacity and ARM64 FAT/VFS buffer capacity
remain blockers. Windows/FreeBSD receipts are incomplete; macOS is postponed,
never excluded. Never accept host `ls`, compiled fixed names, a raw nonce
substring, bootstrap-seed output, or artifact presence as execution proof.
