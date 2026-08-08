# Lane: dict-values — SimpleOS production harden (ex-claude 0bc1049d)

Goal (verbatim opening directive): "save and update research doc and make plan
for pherallel agent which fix or pre task to shared part and each agents do
separated files. make pherallel plan for simple os harden" — followed by the
**SimpleOS production host-OS master plan**, a convergence-and-enforcement
program: one L4-style protection kernel, one typed capability model, one process
and loader pipeline, one async system API, one VFS, one driver protocol, one
service manifest, one configuration engine, and generated compatibility facades.

Plan docs (all present on `origin/main`):
- `doc/01_research/domain/simpleos_production_host_master_plan.md`
- `doc/01_research/local/simpleos_production_host_master_plan.md`
- `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` (Stage S / P1-P8 / INT)
- `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
- `doc/02_requirements/os/posix_profiles.md`, `doc/04_architecture/os/abi/rfc_template.md`

## Plan audit 2026-08-01

### Registry correction
`groups.md` credited `6019def3307`. That commit is
`docs(ui): cross-ref DrawIR v3 packed encoding + GPU-WebScene offload` — two UI
rendering doc files, **unrelated to SimpleOS**. It was merely the last commit at
session exit. The session's own recorded SHAs (`c0231f8`, `624e329`,
`ec53c744`, `9d45f8d`, `e47089d`, `5fbd935`) are all NOT ancestors of
`origin/main` — they were rebased. The content did land, under:
`8eacdf29f2c` (Stage S), `bd0b854606f` + `74df5eb4751` (Stage INT),
`50bb759cae8` + `62ab6ceb94d` (T3-CTR), `e479811c547` (SVC2), `b6234c8b6a0`
(docs). The session's answer to "confirm all three landed on origin" was
verified against the wrong SHAs.

The literal directive (research doc + parallel-agent plan) **is fully done and
landed**. The harden *execution* is a partial, honestly-scoped landing —
`simpleos_production_master_plan_completion_status.md` self-labels its blocked
rows rather than overclaiming.

### MISSING — actionable next steps
1. **Arm the boot seal (highest value).** `_seal_ambient_spawn_on_boot()`
   returns `false` at `src/os/kernel/boot/init_services.spl:47` — the single
   most load-bearing enforcement item is gated OFF. Migrate shell / WM /
   fs-exec spawn callers to `SpawnSpec`, flip the flag, capture a QEMU boot
   transcript.
2. **P1 IPC fastpath.** `l4_fast_ipc.spl` still describes itself as a
   benchmark/model — no syscall or scheduler wiring. Needs real syscall-path
   integration plus two-process QEMU call/reply evidence.
3. **Live child CSpace injection + descriptor-based ELF exec** (master plan
   §24.5, §24.8) — not done. Service capabilities are still strings.
4. **Collapse the VFS.** FAT32 copies went 4 → 3; `fs_driver/fat32_*` and
   `os/services/fat32` still coexist. One VFS is an explicit plan goal.
5. **Build `lld_static`.** No binary under `build/os/llvm/*/bin/`; the gate
   script `scripts/os/ssh_lld_link_uefi.shs` was authored but never run, so
   in-guest linking + execution remains unproven.
6. **Writable shared `mmap()` + POSIX threads** in SOSIX/POSIX — still
   excluded; required by serious ports (OpenSSH, SQLite amalgamation).
7. **Routed HTTP server perf and the full Simple DB server** — still open.
8. **Phase 7 (browser split / origin / cookie / conformance) and Phase 8
   (hardware qualification, secure boot, installer, SBOM)** — entirely blocked.
9. **Interpreter place model** — the user asked for this explicitly. Deliberate
   RED left in tree: `test/01_unit/compiler/two_hop_field_method_mutation_spec.spl`
   fails 4/5, correctly testing an open interpreter defect.

### Verified good
Lean "69 sorry-free theorems" claim holds (no bare `sorry` tactic). Board claim
(Arduino UNO Q, 13/13 GREEN, 3x reproduced, OVMF real-firmware) has a full
documented evidence chain. Artifacts present: `production_status.sdn`,
`abi_v1.spl`, `duplicate_owner_spec.spl`, `vfs_handle_table.spl`,
`os/services/container`, `os/security/llm_profiles`, `lib/common/config_core`,
`src/verification/{os_enforcement,kernel_capabilities}`.

## sspec sufficiency 2026-08-01

**Runner:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(the live `bin/simple` has no `test` subcommand). Harness falsifiability and the
Rust-seed delegation finding are documented once in `layout_web.md`
§"sspec sufficiency 2026-08-01" and apply here too.

### Specs the three landings actually added

`8eacdf29f2c` (Stage S) added 8 specs: `config_layers_spec`,
`duplicate_owner_spec`, `handle_mount_association_spec`,
`abi_v1_transfer_contract_spec`, `spawn_authority_contract_spec`,
`posix_honest_failure_spec`, `llm_profile_attenuation_spec`,
`tty_write_delivery_spec`. `bd0b854606f` (Stage INT) added 3:
`vfs_service_handle_routing_spec`, `spawn_enforcement_wiring_spec`,
`llm_profile_spawn_adapter_spec`. `50bb759cae8` (T3-CTR) added
`container_manager_spec`. **All 12 are `test/01_unit/` — the three landings
added no system-tier spec at all.**

### Coverage verdict

There is **no system test for this lane's goal**. The only
`test/03_system/` file whose name suggests it,
`test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl` (712 lines),
is a GPU/GUI/RTL release-gate matrix: it contains **zero** occurrences of
`spawn_authority`, `SpawnSpec`, or the boot seal, and does not exercise any
convergence item from the master plan.

Nine of the twelve unit specs are genuinely behavioural (they construct
capability tokens, pouches, handles and assert semantics — e.g.
`abi_v1_transfer_contract_spec` proves rights only attenuate and that a rights
mask cannot be used as a back door). Three read source text via `file_read`:
`duplicate_owner_spec` (2 calls), `posix_honest_failure_spec` (3),
`spawn_enforcement_wiring_spec` (3).

**Confirmed false-green — the boot seal.**
`spawn_enforcement_wiring_spec.spl`'s `it("arms the guard at the end of boot
service initialization")` does **not** test that the guard is armed. It
`file_read`s `init_services.spl` and asserts the *text* contains
`spawn_authority_seal_bootstrap` and that `index_of(...)` of the seal call is
greater than the storage/display init positions. That text is present — but it
sits inside `if _seal_ambient_spawn_on_boot():`, and
`src/os/kernel/boot/init_services.spl:47-48` is literally
`fn _seal_ambient_spawn_on_boot() -> bool: return false`. So the spec passes
while the enforcement it names is switched **off** at runtime, exactly as
MISSING item 1 above states. The `it` name asserts a runtime property the
assertions cannot see. (The production code is honest — it logs
`seal DEFERRED` — and `spawn_seal_readiness_spec.spl` is a genuinely
behavioural companion that proves the *sealed-path semantics* for the SHELL /
CONSOLE_SHELL / APP_LAUNCHER recipes. The defect is confined to this one
source-text `it`, but it is the single most load-bearing claim in the lane.)

Missing scenarios — no spec at any tier:
- **QEMU boot transcript with the seal armed** (MISSING item 1). Nothing can
  demonstrate the seal holds in a booted guest; the readiness spec is an
  in-model proof only.
- **P1 IPC fastpath syscall/scheduler wiring** (item 2). `l4_fast_ipc_spec.spl`
  exists but tests the benchmark/model, not a syscall path; there is no
  two-process QEMU call/reply evidence.
- **Live child CSpace injection and descriptor-based ELF exec** (item 3) — grep
  for `cspace_inject`/`child_cspace`/`exec_descriptor` across `test/` returns
  **zero** files.
- **VFS collapse** (item 4) — no spec asserts the single-VFS invariant; the
  duplicate `fat32_*` trees are unconstrained by any test.
- **In-guest `lld_static` link + execute** (item 5) —
  `test/01_unit/os/toolchain/lld_gate_receipt_spec.spl` checks a *receipt*
  shape, not a real link; `scripts/os/ssh_lld_link_uefi.shs` was never run.
- **Writable shared `mmap()` + POSIX threads** (item 6) —
  `vmm_shared_mmap_spec.spl` exists at unit tier only; no SOSIX conformance run.
- **Phases 7 and 8** (items 8) — entirely untested, consistent with "blocked".

### Run results — NOT OBTAINED

The 11 goal-bearing unit specs were queued on the runner above but **produced no
verdicts**, and the batch was abandoned rather than left to churn. The
immediately preceding lane (`l1_pair_b.md`) had just timed out 4 of 4 at 300 s
each, and the control experiment proves why: the 3-example scratch probe that
completed in ~60 s at 04:00 **timed out at 400 s** when re-run at 04:26. Box
load average went 13 → 18 → 42 → **101** during the session, driven by competing
`bootstrap-from-scratch` builds in sibling worktrees
(`simple-redeploy-selfhost-20260731-wt`, `simple-unresname-fable-wt`) saturating
btrfs writeback; our runner was scheduled at ~2 % CPU and even
`simple test --help` exceeded 120 s. Continuing would have produced 11 more
guaranteed timeouts and no information.

**These specs therefore have no pass/fail evidence from this session.** They
must be re-run on a quiet box before any claim about their state. Nothing here
should be read as either confirming or contradicting the lane's green claims.

**Verdict: insufficient on coverage; cannot-run on execution.** The unit tier is
better than average for this repo —
the capability/ABI attenuation specs are real, well-named behavioural proofs —
but the lane's actual goal (a *converged, enforcing* production host OS) has no
system test, its headline enforcement item passes only a source-text assertion
while the flag is `false`, and six of the nine open master-plan items have no
executable coverage of any kind.

## Seal gate status 2026-08-01

**Decision: the boot seal stays OFF. `_seal_ambient_spawn_on_boot()` in
`src/os/kernel/boot/init_services.spl` still returns `false`.**

### What the gate is

`init_all_services()` ends with the master-plan §5.4 ambient-spawn seal:

```
spawn_authority_set_root_task(BOOT_ROOT_TASK_ID)
if _seal_ambient_spawn_on_boot():
    spawn_authority_seal_bootstrap()
```

Sealing closes the bootstrap window: after it, only the root task (`caller == 0`,
the kernel-origin sentinel) may take the ambient `spawn_full()` path in
`syscall_process.spl`. Every other caller must present a SpawnSpec recipe or is
refused `EACCES`.

### Why it is still off — the concrete blocker

`syscall_process._declared_spawn_recipe()` reads the recipe from a **process-wide
scalar** (`spawn_authority_current_recipe()`), not from the syscall arguments,
and carries this TODO in-tree:

> `TODO(boot-seal): carry the recipe id as an explicit syscall argument so a
> genuine ring-3 caller can declare it across the privilege boundary. The scalar
> only propagates for in-image callers (launcher, boot services), which is every
> migrated caller today.`

That is the blocker, and it is an ABI gap, not a flag:

- Syscall 13 (`spawn`) has **no recipe argument**. A ring-3 caller cannot set the
  scalar — it lives in kernel memory and is only written by in-image callers
  (`launcher_registry.spl:428`, `fs_exec_spawn.spl:366/392`).
- So for any genuine ring-3 spawn the declared recipe is `SPAWN_RECIPE_NONE`,
  `spawn_recipe_is_migrated(0)` is false, and the caller falls to the ambient
  path.
- With the seal armed, that ambient path returns `SPAWN_AUTHORITY_EPERM`
  for every `caller != 0`. Net effect of flipping the gate today: **every
  userland syscall-spawn (shell, WM, fs-exec launch) fails `EACCES`** while the
  in-image launcher path keeps working — i.e. an in-guest regression that only
  shows up on a real boot.

Only three recipes exist (`SPAWN_RECIPE_SHELL`, `SPAWN_RECIPE_CONSOLE_SHELL`,
`SPAWN_RECIPE_APP_LAUNCHER`, `spawn_recipes.spl:46-48`), all reachable only from
in-image callers.

### What is NOT the blocker any more

The SEALPREP lane (`78328f8e903`) recorded the arming blocker as
"`_find_source` iterates `parent.caps` while `CapabilitySet.full()` is
`caps: []`, so an ambient parent authorizes NOTHING". That specific defect is
**resolved at HEAD**: `spawn_recipe_seed_parent_caps(recipe, owner)` builds
concrete delegable tokens (`depth: 2`) and is now called on both mint paths
(`syscall_process.spl:157`, `fs_exec_spawn.spl:349`), so a migrated recipe no
longer mints deny-all. The remaining gap is purely the missing recipe argument in
the syscall ABI.

### Evidence still missing

No QEMU boot+launch transcript exists for a sealed boot. Per
`.claude/rules/board-runnable.md` the promotion bar is real-firmware boot
(OVMF pflash) plus a serial transcript showing in-guest shell/WM launch
surviving the seal. Nothing in-tree meets it.

### Promotion checklist (all four required)

1. Carry the recipe id as an explicit syscall-13 argument (removes the
   `TODO(boot-seal)` in `syscall_process._declared_spawn_recipe`).
2. Migrate the ring-3 spawn callers (shell, WM, fs-exec launch) to declare a
   recipe through that argument.
3. Flip `_seal_ambient_spawn_on_boot()` to `true` **and** update
   `test/01_unit/os/kernel/loader/spawn_enforcement_wiring_spec.spl` — its
   "places the seal call last in boot, but leaves it BEHIND AN OFF GATE" case
   asserts the gate is off precisely so the flip cannot land silently.
4. Capture a real-firmware QEMU boot+launch serial transcript with the seal
   armed, and link it here.

### False-green fixed in the same change

`spawn_enforcement_wiring_spec.spl`'s case
*"arms the guard at the end of boot service initialization"* asserted only the
**text position** of `spawn_authority_seal_bootstrap()` inside
`init_services.spl`. The call it located sits inside `if
_seal_ambient_spawn_on_boot():`, which is `return false` — so the spec claimed an
armed guard while boot never armed one. It is now split in two:

- a source-shape case, retitled to what it actually proves, which additionally
  asserts the gate exists and reads `return false`;
- a behavioural case that runs boot's two calls through the guard's own API and
  asserts `spawn_authority_bootstrap_sealed()` and the root-allowed /
  userland-EPERM outcomes, then reopens the window so case order cannot leak
  state.
