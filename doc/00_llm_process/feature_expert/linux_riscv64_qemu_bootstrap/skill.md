# Feature Expert — Linux riscv64 QEMU Bootstrap Lane

## Role

Own process knowledge for bootstrapping Simple natively inside a riscv64
Linux guest (Ubuntu cloud image) under QEMU TCG, on an x86_64 or aarch64
host. Target: an admitted trust-root Stage 2 compiler built *in the guest*
from a `release/*` (or `main`) snapshot, then Stage 3/4 when budget allows.

## Pipeline Links

- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- Sibling lane: [freebsd_qemu_bootstrap](../freebsd_qemu_bootstrap/skill.md)

## Feature Links

- Host wrapper: `scripts/check/check-linux-riscv64-bootstrap-qemu.shs`
  (`--image --start --smoke --provision --sync [REF] --stage2 --ssh --stop`)
- Triple mapping: `scripts/setup/platform-detect.shs` exports
  `PLATFORM_RUST_TRIPLE` (`riscv64-unknown-linux-gnu` -> `riscv64gc-unknown-linux-gnu`);
  `bootstrap-from-scratch.sh` passes it to every `cargo --target` and the
  authority profile dir. Pinned by `scripts/check/check-bootstrap-portability.shs`.
- Guide: `doc/07_guide/platform/misc/platforms.md` § Linux riscv64 QEMU

## Recipe

```bash
# host (Debian/Ubuntu): qemu-system-riscv opensbi u-boot-qemu qemu-utils cloud-image-utils
sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --smoke      # PASS line: arch=riscv64 nproc=20
sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --provision  # rustup nightly + clang/lld in guest
sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --sync origin/release/1.0
sh scripts/check/check-linux-riscv64-bootstrap-qemu.shs --stage2     # detached in guest, polls ~/stage2.rc
```

## Load-bearing facts

- Boot chain is OpenSBI `fw_jump` -> U-Boot S-mode -> the image's own kernel
  (extlinux/EFI). Never `-kernel <linux>`: it is the same firmware chain a
  riscv board uses.
- Default 20 vCPUs (`QEMU_CPUS`), 32G RAM, 160G overlay over a pristine,
  sha256-verified base in `~/.simple/qemu/media`. MTTCG (`thread=multi`).
- **Backend is cranelift.** No LLVM 23 packages exist for riscv64 guests
  (Ubuntu ships 18-21; apt.llvm.org has no riscv64), and the seed's `llvm`
  feature needs 23. `STAGE2_BACKEND` overrides.
- The guest checkout is a `git archive` snapshot with a one-commit local repo
  (bootstrap reads `git` metadata); `~/simple/.source-sha` records the real sha.
- `RISCV_LINUX_VM_DIR` (not `QEMU_VM_DIR`) relocates the VM: the FreeBSD
  wrapper reads `QEMU_VM_DIR` from the same `~/.simple/qemu-host.conf`.
- TCG: correctness evidence only, never timing evidence.

## Traps

- `cargo --target riscv64-unknown-linux-gnu` is not a Rust target; before
  `PLATFORM_RUST_TRIPLE` every riscv64 Linux `--full-bootstrap` died at the
  first cargo call.
- `rust-toolchain.toml` pins `nightly`: `rustup target add` must name
  `--toolchain nightly`, else cross `cargo check` fails `E0463 can't find crate for core`.
- QEMU's default `werror=enospc` pauses a guest silently on a full host disk;
  the wrapper uses `werror=report` and refuses `< QEMU_MIN_FREE_GB` (30).
- `SIMPLE_NATIVE_FILE_TIMEOUT` defaults to 1800 in `--stage2`; the 300s
  default turns slow TCG files into "N file(s) failed to compile".
- `[profile.bootstrap]` is `codegen-units = 1`, so each big crate compiles on
  ONE guest thread: measured 2026-10-03 at 20 vCPUs, guest load ~1.3,
  `simple_compiler` alone ~1.7h and cargo step 1 (`simple-driver`) ~4h.
  For quick riscv64 probes, cross-build the seed on the host instead
  (`cargo build --profile bootstrap --target riscv64gc-unknown-linux-gnu`,
  `CC_riscv64gc_unknown_linux_gnu=riscv64-linux-gnu-gcc`, keep the repo's
  `linker = "clang"`; ~15 min on 80 cores) and copy it into the guest.
- The native link needs `zlib1g-dev libzstd-dev libtinfo-dev` (`-lz -lzstd
  -ltinfo`); the cloud-init package list installs them.
- `__riscv_flush_icache` (glibc, called by libgcc `__clear_cache`) used to be
  weak-stubbed as "unresolved", shadowing the real icache flush; it is now in
  the known-libc list (`native_project/tools.rs`).
- A seed `native-build` probe must run from a git checkout with the program
  under `src/` or `test/` (`SCV-E-ADMISSION: source-inventory-scope-unsupported`)
  and, the first time, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`. Cold inventory under
  TCG exceeded 90 min; cross-build from the host for fast probes.
- First full run (2026-10-03/04, 20 vCPU, cranelift): cargo 10.7h, then
  `check-bootstrap-preflight.shs` re-runs `cargo check --release --bin simple`
  (2.8h, PASS 5/5), then Stage 2 died in seconds with exit 89
  `status=rss-measurement-failed samples=0`: the RSS watchdog's first `ps`
  sample (~560ms + ~330ms perl start on this guest) blew the 1000ms
  `SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS` default. `--stage2` now exports
  5000 (the knob's max; same precedent as `check-phase2-gpu-vulkan-pipeline.shs`).
- To retry Stage 2 without paying the Rust builds again, rerun `--stage2`
  WITHOUT `--sync`: the committed Rust authority for the unchanged snapshot is
  reused (a new snapshot changes the Rust input fingerprint -> full rebuild).
