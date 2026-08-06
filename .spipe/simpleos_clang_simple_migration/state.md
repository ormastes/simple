# Feature: simpleos-clang-simple-migration

## Raw Request

"with spipe dev skill, impl the plan with pherallel agents. let migrate clang and
simple completely to simple os and fix simple os problem during migration."

(Preceding goal established the plan: bootstrap Simple compiler/interpreter/loader
on SimpleOS; recheck clang build + hello-world smoke on the SimpleOS terminal;
in-QEMU clang bootstrap using that clang as seed plus an ormastes llvm/clang fork;
Simple self-bootstrap on SimpleOS; must later run on a real SBC board.)

## Task Type

feature

## Refined Goal

Migrate the clang/LLVM toolchain and the Simple compiler onto SimpleOS so both
compile and run in-guest under real firmware, fixing each SimpleOS defect that
blocks the migration rather than working around it.

Plan of record: `doc/03_plan/os/simpleos/toolchain_selfhost_bootstrap_plan.md`.

## Acceptance Criteria

- AC-1: `github.com/ormastes/llvm-project` branch `simpleos` holds all SimpleOS
  toolchain work (nothing SimpleOS-specific left uncommitted on local disk), and
  `src/os/port/llvm/build.spl` `LLVM_REVISION` equals the fork tip.
  **DONE** — fork tip and pin both `596122063`; verified by `git ls-remote`.
- AC-2: Cross LLVM/clang/lld for `x86_64-unknown-simpleos` builds from source on
  this host, and the outputs are GUEST-RUNNABLE (Type=EXEC, entry 0x40000000,
  zero INTERP segments) — not the Linux-dynamic ELFs stage 2 used to emit.
  **DONE 2026-08-06.** All three stages complete:
  `bin/clang-20` 127,572,072 B sha256 `8554035d57523bbf8a62aedd…`;
  `bin/lld` 64,526,504 B sha256 `bf1da1aece19814a0df3a381…`; both EXEC /
  0x40000000 / 0 INTERP. compiler-rt builtins installed to
  `build/os/sysroot/lib/clang/20/lib/x86_64-unknown-simpleos/`.
  Required fixing three SimpleOS defects (libc runtime-symbol leak, stale
  `libm.a` copy, duplicate `environ`) plus adding `-static` + the SimpleOS
  linker script to the toolchain. The deprecated `clang_static.shs` relink is
  no longer needed for a guest-runnable image.
- AC-3: `bin/release/x86_64-unknown-simpleos/simple` exists as a static ET_EXEC
  ELF64, entry `0x40000000`, proven by `readelf -h`.
  **DONE (STAGING) 2026-08-06** — 2,300,776 B, ELF64 EXEC, entry 0x40000000,
  0 INTERP segments, 0 undefined `rt_*`, sha256 `190b23528e79cfb436250cd8…`.
  Built by the Rust bootstrap seed (sha256 `13ebe5dd22f0cabf…`) per the D1
  route-around, so this is STAGING evidence, NOT self-hosted evidence. The
  payload is **linked, not run** — running it is AC-6/AC-7, blocked on D6.
  Required porting the real Simple runtime (17/20 symbols from
  `src/runtime/runtime_native.c` incl. the whole transient-heap protocol; 3
  written against the verified `RtCoreArray` layout; 1 libc gap). The cheap
  "trim the import closure" alternative was tested and REFUTED.
- AC-4: In-guest compile: fresh OVMF-pflash transcript of `clang -cc1 -triple
  x86_64-unknown-simpleos -emit-obj` producing a byte-exact object, via
  `scripts/os/scp_retrieve_over_ssh_uefi.shs`. (Historical proof exists at commit
  `7cf0b6aec3a`; a fresh run is required.)
- AC-5: In-guest LINK + RUN: `ld.lld` runs inside SimpleOS, links `/HELLO.O` into
  an executable, and FS-exec runs it printing hello on the SimpleOS terminal —
  rungs 3-6 of `scripts/os/ssh_lld_link_uefi.shs`, never executed to date.
  This is the goal-2 exit criterion.
- AC-6: Install-image contract satisfied and proven live: all seven paths
  (`/usr/bin/simple(.smf)`, `/bin/simple(.smf)`, `/sys/apps/simple{,_compiler,
  _interpreter,_loader}(.smf)`, `/SYS/SIMPLETOOL.SDN`) present, and
  `ssh root@guest /usr/bin/simple /hello.spl` returns rc=0 with correct output.
- AC-7: Simple compiles to native IN-GUEST: `/usr/bin/simple --emit-object` then
  in-guest `ld.lld` link then FS-exec run, all inside SimpleOS.
- AC-8: Clang self-compile witness: in-guest `clang_static -cc1` compiles a real
  preprocessed LLVM translation unit to an object, byte-compared against the host
  cross build of the same `.i`.
- AC-9: Every SimpleOS defect found during migration is fixed at its owner layer
  (pure Simple / libc / sysroot) with a bug record and a fail-closed regression
  check — never masked by a stub. Fabricated `rt_*` stubs are forbidden.
- AC-10: Board-runnable status stated honestly: x86_64 real-firmware proxy (OVMF
  pflash, never `-kernel`) for every gate, and the physical-board blockers
  (mini-PC not purchased, no physical NIC driver) remain filed and visible rather
  than implied complete.

## Scope Exclusions

- aarch64 SimpleOS — filed EFI-stub/PE-header gap plus seed arm64 miscompile
  (`doc/08_tracking/bug/aarch64_real_firmware_boot_gap_and_seed_defects_2026-07-14.md`).
- riscv64 clang hosting — the on-hand ML Carrier board has 64 MiB RAM; the clang
  payload alone is ~124 MB. Simple-payload lane only.
- Full in-guest clang self-BUILD (clang building all of clang) — gated behind
  FAT32 write/subdir support, fork/exec on the FS-exec path, and a guest sized
  ≥8 GB RAM / ~20 GB disk. AC-8 is the honest scoped witness instead.

## Cooperative Review

Parallel Sonnet-class implementation lanes, each returning evidence to this
orchestrator (merge owner): C1 cross-LLVM build, S1 Simple payload + runtime
port, C2 doc truth, B2 FAT32 subdirs, B3 fork/exec, C4/C5 link-ladder prep.
Shared interfaces: `src/os/port/llvm/build.shs` stage names
(`host-tools`/`cross`/`compiler-rt`); sysroot layout `build/os/sysroot/{lib,include}`;
gate scripts `scripts/os/{scp_retrieve_over_ssh_uefi,ssh_lld_link_uefi,
ssh_simple_hello_uefi}.shs`. Fail-fast placeholders: spec rows for absent hosts
report `blocked`, never `skip()`. Final reviewer: orchestrator (Opus) before any
PASS claim; no lane may self-certify a goal-level AC.

## Critical blocker — D6 (gates AC-4 through AC-8)

`vmm_kernel_pml4_phys()` reads 0 after a demonstrably successful `vmm_init`, so
`create_user_address_space` falls back to the legacy sentinel and EVERY FS-exec
ring-3 spawn returns `rc=-1`. Found independently by two lanes on the same day.
Serial proof and candidate mechanisms:
`doc/08_tracking/bug/simpleos_vmm_kernel_pml4_phys_reads_zero_after_init_2026-08-06.md`.

Nothing has executed in-guest this session. L1-L3 of the OVMF ladder pass, the
toolchain is built and guest-shaped, and the Simple payload links — but per the
plan's own 2026-07-14 ground truth this state is **staging-proven, not
in-guest-run**. AC-4/5/6/7/8 are all downstream of D6.

## Evidence-integrity hazard to respect in every D6 iteration

`config/freestanding_fabricated_stub_baseline.sdn` has ZERO rows for entry
`simpleos_ssh_ring3_uefi128.elf`, and `stubs.rs:299-314` only WARNS for an
unbaselined entry (it hard-fails on new fabrications only once baselined). Lane
B3 proved this channel silently fabricates weak no-op bodies when a source file
fails to build, yielding a green build with dead code. Consequences:
- Acceptance for a D6 fix must be the POSITIVE marker `[oo-nvme] persist
  /hello.o -> OK`, never the absence of the failure line — a stubbed accessor
  satisfies every absence condition.
- Diff the `FABRICATED-NEW` symbol set before vs after any kernel change.
- Baseline the entry on a known-good PRE-fix build to turn the channel into a
  ratchet.

## Phase

dev-done → implement (in progress)

## Log

- dev: Created state file with 10 acceptance criteria (type: feature).
- F1 DONE: committed 30 freestanding-ification files that existed only on local
  disk; pushed fork to `596122063`; pinned build.spl to match.
- C1: fixed two blocking SimpleOS defects (libc leaked Simple-runtime symbols
  into every C/C++ link; stale `libm.a` copy reproduced the error after the first
  fix). Cross configure now succeeds; clang+lld building.
- B2 DONE: FAT32 subdirectory read traversal, 17/17 spec, sabotage-verified.
- C2 DONE: toolchain guide corrected; drift recorded as a bug.
- S1 BLOCKED: 20 missing `rt_*` symbols; runtime-port lane opened. Also fixed a
  fail-open compiler probe that had accepted a core-dumping builder.
- Landed `8b2e712744c` on main (verified via ls-remote).
