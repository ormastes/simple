# SPM (Simple Process Manager) Feature Requests

Tracker for the `spm-winfs-llm-suite` kernel-side and userland follow-ups that
landed with explicit TODO/stub code. Each entry captures WHY the work was
deferred when the parent feature shipped so the implementer does not relitigate
the decision.

Parent feature ship commits on `origin/main`:
- `7f9efb0856` parser fix
- `f413ca6c30` feature docs + syscall ID reassignment
- `08435d26bd` syscall ID collision fix (100-104 → 110-114)
- `7388fc19f3` real `[u8].ptr()` for SPM syscall buffers
- `17521d1ca5` SPM syscalls 110-114 + `spm_port` primitive
- `ea8ea8fe05` missing handler bodies + `_copy_in_bytes` stub
- `6353c53526` `spm_port_register` wired into `init_services`
- `39817ef665` real `_copy_in_bytes` VA walk

## Open Requests

### FR-SPM-0001 — Page-table-walk read primitive for cross-page / non-identity-physmap user reads

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Code session (SPM follow-up orchestrator)
- **Target:** os-kernel (src/os/kernel/ipc + src/os/kernel/memory)
- **Priority:** P2
- **Status:** Implemented (2026-04-22)
- **Requested-semantics:**
  Expose a `pt_walk(space: ProcessVmSpace, vaddr: u64) -> u64?` (or equivalent
  "translate user VA → kernel-readable pointer") helper in
  `src/os/kernel/memory/vmm.spl`. Consumers:
  `_copy_in_bytes` (src/os/kernel/ipc/syscall.spl), `GrantTable.safecopy_from`
  (src/os/kernel/ipc/capability.spl:564-565), `GrantTable.safecopy_to`
  (capability.spl:588-589). Current implementations all assume identity-mapped
  physmap and deref user VA directly via `*const u8`, which is only safe when
  the VMA happens to live inside the identity-mapped range and the copy does
  not straddle a page boundary into unmapped or differently-permissioned
  memory.
- **Acceptance-criteria:**
  - [x] `pt_walk` returns a physmap-safe kernel pointer (or `nil` on miss /
        non-present / user-bit-missing / execute-only page)
  - [x] `_copy_in_bytes` rewritten to loop one page at a time, translating
        each page and copying the intersection with `[ptr, ptr+len)`
  - [x] `safecopy_from` / `safecopy_to` updated equivalently (remove the two
        existing TODO comments in capability.spl)
  - [x] Cross-page spec: `_copy_in_bytes(vaddr_near_page_boundary, >PAGE_SIZE
        length)` returns the full byte sequence when both pages are mapped
        READ, returns `[]` when the tail page is unmapped
  - [x] No regression in `test/os/kernel/ipc/` or
        `test/os/kernel/fs/win_vfs/`
- **Related-upfront:** `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+
  boundary rules around kernel ↔ user memory)
- **Related-design-doc:** `doc/05_design/spm_pt_walk_user_copy.md`
- **Related-issue:** none
- **Notes:** Implemented 2026-04-22 with explicit `ProcessVmSpace` helpers in
  `src/os/kernel/memory/vmm.spl`: `vmm_pt_walk_user_read`,
  `vmm_pt_range_user_readable`, `vmm_pt_range_user_writable`, and
  `vmm_copyin_bytes_from_space`. `_copy_in_bytes` now uses the explicit-space
  helper for real vmspaces and keeps the pml4=0 fallback only for existing
  early-boot/unit fixtures after VMA validation. Grant safecopy paths reject
  page-table misses when a registered vmspace has a real PML4. Coverage:
  `test/unit/os/kernel/memory/vmm_copyin_spec.spl`,
  `test/unit/os/kernel/ipc/ipc_grants_spec.spl`, and
  `test/system/simpleos_spm_pt_walk_copy_spec.spl`.

### FR-SPM-0002 — Caller-TaskId → privilege-mirror lookup for `sys_priv_check` (case 110)

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Code session (SPM follow-up orchestrator)
- **Target:** os-kernel (src/os/kernel/ipc/syscall.spl +
  src/os/kernel/privilege/privilege_bridge.spl)
- **Priority:** P2
- **Status:** Implemented (2026-04-22)
- **Requested-semantics:**
  `_handle_spm_priv_check` in syscall.spl currently always returns `0` (deny)
  because it has no path from "the syscall that just arrived" to
  `bridge_lookup(caller_task_id)`. Wire the caller's `TaskId` through so the
  handler can call `two_gate_check(bridge_lookup(caller), id_path)` and return
  the real boolean. Likely shape: either `syscall_handler` passes the scheduler
  into the SPM handlers too (it already has `scheduler: Scheduler`), exposing
  `scheduler.current_task_id()`, or a global `g_current_task` is added alongside
  the existing `g_current_vmspace`.
- **Acceptance-criteria:**
  - [x] Handler returns `1` when the caller task has a registered privilege
        mirror whose id-path tree covers the requested id-path bytes
  - [x] Handler returns `0` for no-mirror, mismatched path, or empty id-path
  - [x] Spec: register two tasks with different mirrors, call `sys_priv_check`
        from each, assert the result matches the respective mirror's coverage
  - [x] No regression in `test/os/kernel/ipc/` or privilege_bridge specs
- **Related-upfront:** `doc/04_architecture/privilege_id_system.md`
- **Related-design-doc:** `doc/05_design/spm_priv_check_task_mirror.md`
- **Related-issue:** none
- **Notes:** Depends on FR-SPM-0001 only insofar as the id-path bytes already
  flow through `_copy_in_bytes`; that path works for small id-paths in the
  identity-mapped case today. Implemented by threading `caller.id` into case
  110 and exposing `spm_priv_check_for_task` for direct SSpec coverage. Test:
  `test/system/spm_priv_check_task_mirror_spec.spl`. Research and plan:
  `doc/01_research/local/spm_priv_check_task_mirror.md`,
  `doc/03_plan/sys_test/spm_priv_check_task_mirror.md`.

### FR-SPM-0003 — Rebind syscall for SPM port when real SPM task id is known

- **Filed-on:** 2026-04-18
- **Filed-by:** Claude Code session (SPM follow-up orchestrator)
- **Target:** os-kernel (src/os/kernel/ipc/spm_port.spl +
  src/os/kernel/ipc/syscall.spl + src/os/kernel/types/syscall_types.spl)
- **Priority:** P2
- **Status:** Implemented (2026-04-22)
- **Requested-semantics:**
  Kernel init now registers `SPM_WELL_KNOWN_TASK_ID = 0xfffffff0` via
  `spm_port_register` (see `init_services.spl::init_spm_port` and the
  `6353c53526` commit body). When the real SPM userland task starts, it must
  claim the port under its own scheduler-assigned `TaskId`. `spm_port_register`
  currently rejects a second distinct task id by design (last-writer-wins
  disabled), so the claim path must call `spm_port_reset` first. That means
  either:
  (a) a new syscall `SysSpmClaim` (id 115?) that the SPM task calls once at
  startup — kernel verifies the caller has the "become-SPM" capability, calls
  `spm_port_reset` then `spm_port_register(caller_task_id)`; or
  (b) extending `SysWinRegister` (111) with an "also claim" flag. Prefer (a);
  it's explicit and auditable.
- **Acceptance-criteria:**
  - [x] New syscall `SysSpmClaim` in `syscall_types.spl` (next free id after
        114 unless reservations dictate otherwise)
  - [x] Handler `_handle_spm_claim` in `syscall.spl` — capability-gated,
        returns 0 on success, `-1` on capability denial, `-2` on already-claimed
  - [x] Spec: unclaimed-at-boot → well-known-id; claim succeeds once; second
        claim from same task is idempotent; claim from different task is
        rejected unless `spm_port_reset` has been called
  - [x] Userland wrapper `sys_spm_claim()` in
        `src/os/userlib/syscall_raw.spl`
  - [x] SPM service (`src/app/simple_process_manager/main.spl`) calls the
        wrapper in its startup path
  - [x] Update `doc/07_guide/tooling/llm_approval_flow.md` with the rebind step
- **Related-upfront:** `doc/04_architecture/simple_process_manager.md` §§
  lifecycle + bootstrap
- **Related-design-doc:** `doc/05_design/spm_claim_rebind.md`
- **Related-issue:** none
- **Notes:** Implemented with syscall id 115 and an existing privilege-mirror
  gate: `id.system` covers the required `id.system.spm.claim` path. The claim
  operation accepts the boot placeholder owner, clears stale placeholder inbox
  state, assigns the caller task id, is idempotent for the same task, and
  rejects a second real owner with `-2`. Test:
  `test/system/spm_claim_rebind_spec.spl`. Research/design/plan:
  `doc/01_research/local/spm_claim_rebind.md`,
  `doc/05_design/spm_claim_rebind.md`,
  `doc/03_plan/sys_test/spm_claim_rebind.md`.

## Id scheme

- `FR-SPM-####` — requests targeting Simple Process Manager and its
  kernel-side port plumbing. Monotonic; do not reuse even after `Rejected`.

## Lifecycle

See `TEMPLATE.md` — `Open` → `Accepted` → `Implemented` (with design-doc or
issue link) or `Rejected` (one-line reason).
