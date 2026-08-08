# Multiarch QEMU Systest — Remaining Lanes Plan (riscv32 / arm32 / x86_64)

**Status:** COMPLETE as of 2026-06-14. The original 6 QEMU lanes are green
(riscv64, arm64, x86_32, arm32, riscv32, x86_64). The added aarch64-darwin hosted
lane is honestly platform-scoped: green on Apple Silicon and `missing-media` on
Linux. This file is now the completion record for the remaining-lanes push, not an
open work queue.

**Goal framing (Stop-hook):** "remake plan for remains with tests and parallel agents
(Sonnet impl, Haiku where mechanical, Opus review). Full detail plan and impl."

## Definition of done (honest, per advisor)

`missing-media` is a RED diagnosed failure — **never** `skip()`, never weaken a spec,
never convert a marker requirement. Each lane lands at exactly one of these honest
states, recorded in this doc and verified by Opus against the **committed** serial log
with binary-safe matching (`grep -a` — `ugrep` skips NUL-containing logs):

| State | Meaning |
|-------|---------|
| `GREEN` | kernel built + boots + ALL contract markers on the wire + spec passes |
| `MARKERS-PARTIAL` | boots, some markers present, blocked at specific named marker |
| `BOOTS` | kernel built + serial output, no acceptance markers yet |
| `BUILT` | kernel ELF links (0 unresolved), does not boot |
| `BLOCKED:<X>` | cannot build; specific blocker named |

The session goal is satisfied by **plan committed + each lane driven to its honest
state with the blocker named** — not only by 3/3 GREEN. The final state exceeded
that floor: the 3 remaining QEMU lanes are GREEN, and the hosted Darwin lane records
its Linux `missing-media` result honestly.

## Shared facts (all 3 lanes)

- **Contract:** `src/os/qemu_systest_contract.spl` (kernel path, image path, qemu bin,
  qemu args, markers, timeout per arch). The contract now includes the settled x86_64
  NVMe/FAT32 model and the aarch64-darwin hosted lane.
- **Build target reference data:** `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl`
  (`qemu_acceptance_lane` per platform). riscv32, arm32, x86_64, and aarch64-darwin
  targets are declared.
- **Specs:**
  - `test/03_system/os/qemu/sys_qemu_riscv32_fs_exec_spec.spl`
  - `test/03_system/os/qemu/sys_qemu_arm32_fs_exec_spec.spl`
  - `test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl`
  Each asserts `classification == SYSTEST_PASS`; missing kernel → `missing-media:<path>`
  → spec fails (correct RED). These specs now pass against committed-source evidence.
- **Build recipe (proven on arm64):**
  ```
  env SIMPLE_BOOT_MINIMAL=1 \
    src/compiler_rust/target/debug/simple native-build \
    --source build/os/generated --source src/os --source examples/09_embedded/simple_os \
    --backend cranelift --opt-level=aggressive --log on --entry-closure \
    --entry <ARCH_ENTRY.spl> --target <TRIPLE> \
    -o build/os/<OUTPUT.elf> --linker-script <ARCH_LINKER.ld>
  ```
  UNSET `SIMPLE_ALLOW_FREESTANDING_STUBS` first (weak no-op defsyms are injected
  unconditionally by linker.rs — judge unresolved by `nm`, not link success).
  Builds get killed under heavy parallel-Codex load → run **nice'd, in background,
  with retries**, not inline.
- **Disk images:** `build/os/fat32-<arch>.img` already exist for all 6 arches
  (verified present). riscv32/arm32 lanes consume them via virtio-blk. x86_64 uses
  the resolved NVMe/FAT32 model.
- **Known 32-bit ABI bug class (from arm64 Path B):** the freestanding runtime passes
  Simple arrays as RAW untagged pointers, so `.len()` / `arr[i]` / module-level `val`
  (tagged-only reads) mis-read. Fix with `rt_arm_array_len_u32` /
  `rt_arm_array_get_byte_u32` + function-local literals. Expect this to recur on
  riscv32 and arm32.

## VCS discipline (mandatory — from memory)

- Work on `main`. Never branch. Each agent owns a **disjoint arch dir**:
  `examples/09_embedded/simple_os/arch/<arch>/**` + the arch-specific loader
  (`src/os/kernel/loader/<arch>_*`). 
- **Commit immediately** after each lint-clean working sub-step — parallel jj reconcile
  clobbers uncommitted Edit-tool changes within ~1 min ("change was intentional"
  reminders during this are reconcile artifacts, NOT user intent). Verify the COMMIT
  (`git show SHA:path | grep`), not just the working copy.
- `_SimpleosMultiplatformBuild/platform_target_catalog.spl` is **shared** — only the x86_64 agent edits
  it (to add the fs_exec target). riscv32/arm32 agents must NOT touch it.
- Push via git-plumbing single-file commits over SSH (`~/.ssh/id_ed25519_this_mac`)
  to survive non-fast-forward races; verify with `git ls-remote`.

---

## Lane A — arm32 (lowest effort, start here)

**Output:** `build/os/simpleos_arm32_fs_exec.elf` · **qemu:** `qemu-system-arm` -M virt
-cpu cortex-a15, loader device `addr=0x40200000` (RawLoader, no `-kernel`).
**Markers:** `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `TEST PASSED`.

**Final state:** GREEN. Entry, linker, boot sources, build target, virtio-blk init,
and contract markers are present. Evidence: `build/os/systest/arm32.serial.log` and
`test/03_system/os/qemu/sys_qemu_arm32_fs_exec_spec.spl`.

**Steps:**
1. Build `simpleos_arm32_fs_exec.elf` with the recipe (triple `arm-unknown-none-eabi`
   or as the arm32 contract specifies; confirm via `_arm32_c_flags`). `nm` for unresolved.
2. Resolve link (32-bit ABI deltas, raw-array helpers — mirror arm64 fixes in
   `arch/arm32/boot/baremetal_stubs.c` + `src/os/kernel/loader/arm_fs_exec_spawn.spl`).
3. Boot under `qemu-system-arm` virt + loader device; capture serial.
4. Wire the 4 contract markers onto the live success path (real load/launch proof, as
   arm64's `arm64_fs_exec_load_and_launch_hello_world` does). Do NOT print markers
   unconditionally — each must assert a genuine capability.
5. Run `sys_qemu_arm32_fs_exec_spec.spl`; classify with `grep -a`. Commit per step.

## Lane B — riscv32 (medium; port the passing riscv64 smf_fs)

**Output:** `build/os/simpleos_riscv32_smf_fs.elf` · **qemu:** `qemu-system-riscv32`
-M virt -cpu rv32 -bios none -kernel.
**Markers:** `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `TEST PASSED`.

**Final state:** GREEN. The rv32 lane uses the shared smf_fs path, auto-selects the
LLVM backend, emits the full marker set, and boots under QEMU. Evidence:
`build/os/systest/riscv32.serial.log` and
`test/03_system/os/qemu/sys_qemu_riscv32_fs_exec_spec.spl`.

**Steps:**
1. Diff `arch/riscv64/smoke_entry.spl` vs `arch/riscv32/smoke_entry.spl`; align the
   rv32 entry to emit the same markers via the same shared smf_fs code path.
2. Build with triple `riscv32-unknown-none-elf`, `_riscv32_c_flags`, `-nostdlib -static`.
   `nm` for unresolved; port any missing riscv64 runtime helpers to rv32
   (`arch/riscv32/boot/baremetal_stubs.c`).
3. Boot `qemu-system-riscv32 -bios none`; debug rv32 virtio-blk + FAT32 (32-bit MMIO,
   pointer width, raw-array helpers).
4. Drive markers to parity with riscv64; run `sys_qemu_riscv32_fs_exec_spec.spl`;
   classify `grep -a`. Commit per step.

## Lane C — x86_64 (highest effort; author entry + target + resolve disk)

**Output:** `build/os/simpleos_x86_64_fs_exec.elf` · **qemu:** `qemu-system-x86_64`
-cpu qemu64 -m 512M -nographic with the resolved NVMe/FAT32 disk model.
**Markers:** `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `TEST PASSED`.

**Final state:** GREEN. The fs_exec entry, build target, and NVMe/FAT32 disk model
are in place. Evidence: `build/os/systest/x86_64.serial.log` and
`test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl`.

**Resolved questions:**
- **O1 — disk model:** resolved as NVMe + FAT32.
- **O2 — build target:** resolved by adding the x86_64 `qemu_acceptance_lane`.

**Steps:**
1. Author `arch/x86_64/fs_exec_entry.spl` mirroring x86_32's
   `initrd_fs_exec_probe_entry.spl`, adapted to 64-bit + the chosen disk model.
2. Add the build target (O2). Build with `x86_64-unknown-none` + `_x86_64_c_flags`.
3. Boot `qemu-system-x86_64`; resolve O1; drive markers; run
   `sys_qemu_x86_64_fs_exec_spec.spl`; classify `grep -a`. Commit per step.

---

## Orchestration

- **Opus (this session):** writes/owns this plan; pre-stages any shared-file edit
  (x86_64 build target / contract disk arg) to avoid clobber; dispatches the 3 Sonnet
  agents with disjoint scope; **independently re-verifies** every claimed PASS against
  the committed serial log with `grep -a`; redispatches on partial; updates this doc +
  memory; runs the final multiarch sweep.
- **Sonnet (×3, parallel):** one per lane (A/B/C) — the load-bearing freestanding
  bring-up + debugging. Each: builds nice'd/background with retries, commits per
  working sub-step, reports honest per-lane state, has `advisor()` access.
- **Haiku (mechanical):** final multiarch systest re-run + per-arch serial-log
  collection/classification (`grep -a`), and any pure scaffolding copy.

## Tests / verification

- Per-lane spec: `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl` must move
  from RED(`missing-media`) → GREEN(`SYSTEST_PASS`) for any lane declared GREEN.
- Full sweep: rebuild + boot all 6 lanes; classify each with `grep -a`; expect the 3
  existing greens to stay green and report honest state for the 3 targets.
- Evidence: `build/os/systest/<arch>.serial.log` (committed-source reproduction) +
  this doc's per-lane state table.

## Risk / honesty notes

- Each 32-bit lane may surface a full freestanding-runtime-ABI port (arm64 Path B was
  multi-session). If a lane proves multi-session, its honest state (e.g. `BOOTS` /
  `MARKERS-PARTIAL`) is the deliverable for this session, with the blocker named — not
  a forced or faked green.
- No `skip()`, no weakened asserts, no unconditional marker prints, no TODO→NOTE.

---

## FINAL STATE — 2026-06-14 (all lanes settled)

All 3 target lanes reached **GREEN**, plus the 7th (darwin) lane added and the
duplication removed. Every lane independently re-verified by Opus (binary-safe
`grep -a` on the committed serial log) and every green-making source confirmed on
origin — each agent's commits were lost to parallel reconcile and re-pushed via
git-plumbing.

**Codex verification refresh — 2026-06-14:** confirmed this completion record
against the current workspace. `bin/simple test --mode=interpreter` passes for all
six QEMU lane specs:
`sys_qemu_riscv64_fs_exec_spec.spl`, `sys_qemu_arm64_fs_exec_spec.spl`,
`sys_qemu_x86_32_fs_exec_spec.spl`, `sys_qemu_arm32_fs_exec_spec.spl`,
`sys_qemu_riscv32_fs_exec_spec.spl`, and `sys_qemu_x86_64_fs_exec_spec.spl`.
`scripts/check-simpleos-native-surface.shs` reports `STATUS: PASS`, and
`find doc/06_spec -name '*_spec.spl' | wc -l` reports `0`.

| Lane | State | Build/boot notes |
|------|-------|------------------|
| riscv64 | **GREEN ✅ (source-reproducible 2026-06-14)** | root cause: accidental `arch/riscv64/boot/freestanding_runtime.c` `#include`-ing the 100 KB networking runtime, compiled in via the linker boot-dir glob + minimal allowlist (78→175 KB, displaced reset vector). Renamed → `full_networking_runtime.c` (`ab37912`). x86 `glass_render.c` symlink also removed. Verified: fresh 78 KB build, real OpenSBI boot, 6/6 markers. Bug closed |
| arm64 | GREEN ✅ (source-reproducible 2026-06-14) | `arch/arm64/boot/glass_render.c` was a symlink to the x86_64 157 KB GUI file (boot-dir glob pulled it in); removed (`3027ff15`); rebuilds green from source, 7/7 markers |
| x86_32 | GREEN | unchanged |
| arm32 | GREEN ✅ | rebuilt; virtio-blk init fix (`fc1c73a`) |
| riscv32 | GREEN ✅ | LLVM backend **auto-selected** for rv32 by the driver (`d319068`, cranelift blocks rv32); rebuilt green |
| x86_64 | GREEN ✅ | NVMe + FAT32 (O1 ratified, `0c4561b`); rebuilt green |
| aarch64-darwin | hosted — RED on Linux (honest `missing-media`), GREEN on Apple Silicon | 7th platform; merged into contract + build matrix; both files check OK |

**Duplication removed (−~830 L owned code, verify-or-revert):**
- riscv: `arch/common/riscv_common.h` (−360 L ×2) + `linker_riscv_common.ld`
  (−50 L ×2). riscv32 build-verified; riscv64 static-equivalence verified.
- arm: `arch/common/linker_arm_common.ld` (fs_exec linker pair). arm32 build-verified;
  arm64 static-equivalence verified. Tier 2b already shared; Tier 2c skipped
  (EL0-adjacent, ~15 L). Contract-table tier 4 BLOCKED by interpreter struct-array
  hang (see `duplication_analysis.md`).
- contract spl (Tier 1, landed 2026-06-14, origin tip `fd51c63`): shared
  `default_qemu_timeout_ms()` (1a — 6 QEMU lanes delegate, darwin keeps 15000) +
  `standard_smf_markers()` (1b — riscv32/arm32/x86_64 delegate the identical 5-marker
  set; riscv64/arm64/x86_32/darwin keep their distinct sets). Interpreter
  `[text]`-helper-delegation probed safe; marker literals byte-identical (git diff);
  `simple check` OK. Tier 1 now fully complete; safe dedup plan exhausted (only the
  documented-BLOCKED tier 4 remains).

**Reproducibility caveats — RESOLVED 2026-06-14:** riscv64 regression fixed
(accidental boot-dir wrapper renamed); arm64 rebuild env fixed (x86 `glass_render.c`
symlink removed); riscv32 LLVM-driver requirement fixed (driver auto-selects LLVM
for rv32). **Boot-dir-glob footgun — RESOLVED 2026-06-14 (gated):** `linker.rs`
auto-globs every `.c`/`.S` in `arch/<arch>/boot/`, so a stray wrapper or cross-arch
symlink is silently compiled in (the riscv64 + arm64 root cause). Rather than rewrite
the core glob (manifests were incomplete → would break every lane), the existing
`native_surface_policy_verify` is now a fail-closed gate: per-lane boot-source
manifests completed (15 sources), verifier `find` catches symlinks, gate script
`scripts/check-simpleos-native-surface.shs` wired into pre-commit. Verified planted
symlink + stray `.c` both fail. Dedup tier 4 still BLOCKED by the interpreter
struct-array-literal hang.

**Full-sweep clean-rebuild re-verification — 2026-06-14 (per-lane worktree rebuilds):**
Re-ran the plan's "rebuild + boot all 6 lanes" step via isolated git worktrees
(clean `build/os/`), to prove source-reproducibility rather than trust on-disk ELFs.
This surfaced a real regression the stale-ELF boots had masked.

| Lane | Clean-rebuild result | Notes |
|------|----------------------|-------|
| riscv64 | **GREEN (reproducible)** | 80 KB ELF, 0 unresolved, OpenSBI boot, 6/6 markers |
| x86_64 | **GREEN (reproducible)** | 269 KB ELF, 0 unresolved, NVMe→FAT32→SMF, 5/5 + SMF_FS_PASS |
| arm64 | **was RED → FIXED → GREEN (reproducible)** | clean cranelift build hit `undefined symbol: rt_pool_safepoint` (regression from the multicore-green loop-safepoint work — the cranelift backend emits the call at loop lowering, but only x86_64's freestanding stub defined it). Fixed by adding the no-op stub to arm64 (origin `8c8128fa815`, scoped down to arm64-only in the follow-up once the sweep showed no other lane references it); rebuilt 1880 KB ELF, 0 unresolved, **boots 7/7 markers incl genuine EL0 `user-svc-exit:ok`**. Bug `freestanding_rt_pool_safepoint_undefined_2026-06-14`. |
| arm32 | **GREEN (reproducible)** | LLVM backend; clean rebuild from committed source → 153 KB ELF32 ARM, 0 unresolved, 5/5 markers, genuine crt0→UART→FS→SMF→TEST PASSED boot. Does **not** reference `rt_pool_safepoint` (LLVM never emits it). |
| riscv32 | **GREEN (reproducible)** | LLVM backend; clean rebuild with an `--features llvm` driver built from committed Rust source → 33 KB ELF, 0 unresolved, 5/5 markers. Does not reference the safepoint symbol. |
| x86_32 | **GREEN (reproducible)** | LLVM backend (no 32-bit x86 cranelift); the verifying agent **built the LLVM-enabled driver from committed source** then built a fresh 8.5 MB ELF, 0 unresolved, 5/5 markers. |

**Net: 6/6 QEMU lanes GREEN and reproducible-from-committed-source** (+ darwin
hosted, RED-on-Linux by design). The full sweep's value: it caught a real arm64
regression (`rt_pool_safepoint`) that booting stale ELFs had masked, and confirmed
the fix is needed on arm64 only (cranelift-emitted symbol; LLVM lanes and riscv64's
lighter smf_fs kernel never reference it). The LLVM lanes require an `--features llvm`
driver built from committed Rust source (system LLVM 18.1.8 present) — a one-time
toolchain build, not a source change.

**riscv64 independent re-verification — 2026-06-14:** rebuilt clean in a fresh git
worktree off committed `origin/main` (zero pre-existing `build/os/*.elf`): seed-built
ELF 80,144 B (clean ~78 KB, not the 100 KB+ networking-runtime blob), 0 unresolved
symbols (`nm`), real OpenSBI v1.3 boot → `FS_MOUNT_OK` → `SMF_DISCOVERY_OK` → ELF load
→ CLI/GUI launch → render → all 5 markers + `SIMPLEOS_RISCV_SMF_FS_PASS`. Confirms the
lane is reproducible-from-source (not an orphaned artifact); origin tree carries
`full_networking_runtime.c` (96 B) with no `freestanding_runtime.c` in the boot-glob
dir. Reproduction log: `build/os/systest/riscv64_source_reproduction_2026-06-14.serial.log`.
