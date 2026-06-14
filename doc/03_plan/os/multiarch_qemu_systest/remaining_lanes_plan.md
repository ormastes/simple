# Multiarch QEMU Systest — Remaining Lanes Plan (riscv32 / arm32 / x86_64)

**Status:** 3/6 lanes green (riscv64, arm64, x86_32). 3 lanes report `missing-media`
because their kernel ELFs are not built. This plan drives the 3 remaining lanes to
green — or to an honest, documented blocker — via parallel per-arch agents reviewed
by Opus.

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
state with the blocker named** — not only by 3/3 GREEN. We do not promise 3/3; we
promise honest, verified progress with no cover-ups.

## Shared facts (all 3 lanes)

- **Contract:** `src/os/qemu_systest_contract.spl` (kernel path, image path, qemu bin,
  qemu args, markers, timeout per arch). Already correct — **do not edit** unless a
  marker set is genuinely wrong; coordinate first (shared file).
- **Build target reference data:** `src/os/port/simpleos_multiplatform_build_part2.spl`
  (`qemu_acceptance_lane` per platform). riscv32 + arm32 targets already declared;
  x86_64 fs_exec target is **absent** and must be added.
- **Specs (already exist, currently RED):**
  - `test/03_system/os/qemu/sys_qemu_riscv32_fs_exec_spec.spl`
  - `test/03_system/os/qemu/sys_qemu_arm32_fs_exec_spec.spl`
  - `test/03_system/os/qemu/sys_qemu_x86_64_fs_exec_spec.spl`
  Each asserts `classification == SYSTEST_PASS`; missing kernel → `missing-media:<path>`
  → spec fails (correct RED). No spec edits needed — the work is making them pass.
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
  (verified present). riscv32/arm32 lanes consume them via virtio-blk. x86_64 lane
  qemu args currently carry **no disk** — see x86_64 task O1.
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
- `simpleos_multiplatform_build_part2.spl` is **shared** — only the x86_64 agent edits
  it (to add the fs_exec target). riscv32/arm32 agents must NOT touch it.
- Push via git-plumbing single-file commits over SSH (`~/.ssh/id_ed25519_this_mac`)
  to survive non-fast-forward races; verify with `git ls-remote`.

---

## Lane A — arm32 (lowest effort, start here)

**Output:** `build/os/simpleos_arm32_fs_exec.elf` · **qemu:** `qemu-system-arm` -M virt
-cpu cortex-a15, loader device `addr=0x40200000` (RawLoader, no `-kernel`).
**Markers:** `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `TEST PASSED`.

**Current state:** entry (`arch/arm32/fs_exec_entry.spl`), linker
(`fs_exec_linker.ld`), boot (`baremetal_stubs.c`, `crt0.s`, `baremetal_interrupt_control.S`)
and build target all present. Prior build artifact
`simpleos_arm32_fs_exec_nostubs_probe.elf` (May 13) exists → build path was exercised.
**Gap:** the entry emits `[arm-fs-exec]…`/`process-backed:ok` markers, NOT the 4
contract markers (`ELF_LOAD_OK` etc.). Mirror the arm64 marker reconciliation.

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

**Current state:** entry = `arch/riscv32/smoke_entry.spl`, linker =
`arch/riscv32/linker.ld`, boot = `arch/riscv32/boot/baremetal_stubs.c` — all present.
The **passing** riscv64 lane uses the identical structure
(`arch/riscv64/smoke_entry.spl` → `simpleos_riscv64_smf_fs.elf`). So the work is a
32-bit port of the working riscv64 smf_fs kernel.

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
-cpu qemu64 -m 512M -nographic **-kernel only (no disk/initrd in current args)**.
**Markers:** `ELF_LOAD_OK`, `SMF_CLI_LAUNCH_OK`, `SMF_WM_GUI_LAUNCH_OK`,
`NATIVE_GUI_PROCESS_RENDER_OK`, `TEST PASSED`.

**Current state:** NO fs_exec entry, NO fs_exec build target. x86_64 has a mature boot
(`boot_stage1..4_entry.spl`, SMP, paging, `boot/` with crt0/context_switch/syscall).
The x86_32 sibling passes via `initrd_fs_exec_probe_entry.spl` + `-initrd`.

**Open questions (resolve before coding):**
- **O1 — disk model:** x86_64 qemu args have no `-initrd`/`-drive`. Either (a) add
  `-initrd build/os/fat32-x86_64.img` to the contract args (shared-file edit — Opus
  coordinates) mirroring x86_32, or (b) make the kernel self-contained (embedded
  payload, load-proof only like riscv64/x86_64's documented bar). Decide via what the
  markers can honestly assert.
- **O2 — build target:** add an `x86_64` `qemu_acceptance_lane` to
  `simpleos_multiplatform_build_part2.spl` (entry + `linker.ld` + output
  `simpleos_x86_64_fs_exec.elf` + boot sources already listed for x86_64).

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
