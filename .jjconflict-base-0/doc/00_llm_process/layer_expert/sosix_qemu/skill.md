# SOSIX/QEMU Layer Expert

Canonical settings live behind `src/os/qemu_systest_contract.spl`; execution belongs to `src/os/_QemuRunner/`. Refactors may split private modules but must not create a second argv/settings owner.

Required matrix: Linux, Windows, macOS, FreeBSD hosts; x86, ARM, RISC-V guests at 32 and 64 bits. TCG proves correctness only. Native accelerator claims require the retained executed argv and available KVM/HVF/WHPX.

Every row must retain boot and mount identity, in-guest `ls`, arbitrary filesystem program stdout/rc, hashes, exact argv, and serial transcript. Fixed-command fixtures, host commands, source grep, and artifact presence are not execution proof.

Resolve large artifacts through `scripts/qemu/simple-big-storage-root.shs`; never embed `/mnt/data` or `$HOME` in a lane. `SIMPLE_BIG_STORAGE_ROOT` overrides the config selected by `SIMPLE_BIG_STORAGE_CONFIG` (default `.simple-big-storage-root`), then `$HOME/.simple`.

Resolve host binaries and accelerator classification through `scripts/qemu/simple-qemu-settings.shs`. Guest argv remains owned by `src/os/qemu_systest_contract.spl`; the shell preflight must not grow a second descriptor catalog.

Run `sh scripts/check/check-simple-qemu-settings.shs` before evidence. Development selects one six-way `--guest`; release uses mutually exclusive `--all-guests`. Aggregate exactly 24 unique cells with `src/os/sosix/qemu_evidence/matrix_contract.spl`. PASS proves boot, mount, target-side `ls`, and arbitrary filesystem-program execution; nonpass retains reason, artifact, resume, owner, and reviewer.

Primary plan: `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md`. Operator guide: `doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`.

Current admission snapshot (2026-08-12): **0 PASS / 24**. Linux x86_32,
ARM32, RISC-V32, and RISC-V64 have diagnostic target-nonce, live FAT-dirent
listing, and filesystem-program transcripts, but incomplete lineage keeps them
non-PASS. Use `scripts/check/rebuild-sosix-qemu-media.shs --plan|--run --rows
...` for rebuild-only work and `scripts/os/prepare_qemu_nonce_media.shs` for
per-run clones. Neither diagnostic capability nor fixed-name output is PASS.
