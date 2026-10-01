# Feature: simple_os_enhance

## Raw Request

`$sp_dev impl simple os enhancement plan. make a pherallel dev plan and go.`

The supporting assessment is recorded in
`doc/01_research/local/simple_os_enhance.md`.

## Task Type

feature

## Refined Goal

Make SimpleOS's service, process, container, and agent-security models live through one capability-confined execution model, starting with a canonical caller context and a real PID1-supervised workload path.

## Acceptance Criteria

- AC-1: `doc/03_plan/agent_tasks/simple_os_enhance.md` assigns the seven non-overlapping implementation lanes, their frozen interfaces, dependencies, merge owner, review owner, and per-lane evidence command.
- AC-2: Every security-sensitive syscall, spawn, exec, and filesystem-exec path accepts or derives one immutable `KernelCallContext`; a focused authority-path test proves a real caller capability set reaches the filesystem-exec gate.
- AC-3: Live process creation injects a concrete child CSpace into the created task; after PID1 starts, ambient full-authority spawning is sealed, and focused tests prove attenuation, generation revocation, and cross-instance isolation.
- AC-4: A filesystem-backed ring-3 PID1 service manager loads signed workload manifests, orders readiness dependencies, supervises restart/quarantine, and replaces stale grants before restart. A QEMU system scenario proves the VFS → network → HTTP dependency chain and crash/restart behavior.
- AC-5: Each workload task is bound to one isolation and resource domain; VFS, process/PID, IPC, network, syscall, and device paths fail closed across domains and enforce hierarchical limits, evidenced by system scenarios.
- AC-6: Container and agent manifests compile through the same `WorkloadManifest` and policy compiler into a `SpawnSpec`; a rootless container lifecycle and a capability-confined agent/subagent flow both execute through the live process path.
- AC-7: The strong sandbox tier, formal invariants, fuzzing, power-failure, and cross-host QEMU evidence remain explicit active criteria until their required prepared hosts/tools run them; any unavailable row has an open tracking record and exact resume command, never a PASS claim.
- AC-8: Knowledge artifacts remain current: research, requirements, architecture, detail design, test plan, agent plan, generated/manual SPipe docs, relevant `doc/07_guide`, and feature/layer expert skills are updated; every uncovered runtime gap gets a `doc/08_tracking/bug/` record with file:line and unblock condition. Workflow skills/commands are N/A because this feature does not change SPipe behavior.
- AC-9: Each implemented acceptance criterion has one focused passing SPipe/unit/system result; final verification runs the required direct-runtime guards and generated-spec layout guard without introducing raw runtime/env/process calls outside their owner modules.

## Scope Exclusions

- This lane does not claim Docker-equivalent isolation, native strong-sandbox escape resistance, or all-host QEMU PASS until the corresponding runtime implementation and prepared-host evidence exist.
- POSIX-complete user/session, package/update, desktop-session, and physical-board completion follow the P0/P1 capability-enforcement foundation.

## Cooperative Review

- Sidecars: process/CSpace discovery; PID1/service discovery; isolation/container/policy discovery.
- Merge owner: `/root`.
- Final reviewer: `/root` (highest-capability review before requirements, design, implementation acceptance, and manual quality decisions).
- Frozen shared interfaces: `KernelCallContext`, `PrincipalId`, `JobId`, `CspaceId`, `IsolationDomainId`, `ResourceDomainId`, `WorkloadManifest`, and `CompiledExecutionPolicy`.
- Manual flow helpers: `step("Start capability-confined PID1")`, `step("Start dependent workloads")`, `step("Crash and revoke stale grants")`, `step("Verify cross-domain denial")`, and `step("Reap the workload tree")`.
- Setup/checker helpers: `setup_kernel_call_context`, `setup_workload_manifest`, `check_authority_trace`, `check_fresh_restart_grants`, and `check_isolation_denial`.
- Fail-fast placeholders: any unimplemented shared helper returns `fail("simple_os_enhance helper is not implemented")`; no sidecar may silently pass or add a permissive fallback.
- Generated-manual review owner: `/root` after system specs are authored.

## Phase

dev-in-progress

## Log

- dev: Created state file with 9 acceptance criteria (type: feature).
- research/design: Merged three read-only parallel discovery reports. The
  initial implementation boundary is `cap_exec_gate`; concurrently edited
  syscall/ABI and architecture files remain external ownership.
- impl: Added the Phase 0 `KernelCallContext` contract and context-based
  filesystem-exec authorization tests. Live syscall-dispatch construction and
  CSpace injection remain active Lane A work.
- critical-mode: The user elevated this to mission-critical implementation.
  Current evidence tier is focused host execution only. The active safety
  invariants are fail-closed missing context, fork attenuation, and denial of
  ambient authority propagation; QEMU, formal, and release-gate rows remain
  active and cannot be inferred from host tests.
- critical-mode verification: `check-simpleos-mission-critical-release.shs`
  is blocked by nine stale hardening reports (including shared WM, CPU SIMD,
  LLVM port, and GUI/RenderDoc evidence) and did not produce its required
  status record. This is global blocker evidence, not a defect in the focused
  authority slice and not a release PASS.
- verification: focused cap-gate and scheduler specs were executed with the
  currently deployed bootstrap-seed CLI (diagnostic only); focused lint,
  direct-env-runtime guards (working and staged), generated-spec layout, and
  scoped whitespace checks completed without a lane finding.
- coordination: a current review confirms that the concurrently modified ABI
  and syscall files add owned IPC v1 paths but do not yet consume
  `KernelCallContext`. This lane preserves their ownership; the next merge is
  a dispatcher-owned construction of the context from the live scheduler TCB.
- impl: The shared `_handle_exec_state` seam (used by both model dispatch and
  the direct C ABI exec shim) now constructs a context from `get_current()` and
  the real current TCB capabilities. It returns EACCES for no current TCB or
  a missing FileExec/ProcessSpawn pair; the direct-handler regression proves
  this cannot be masked by the model IPC dispatcher's capability check.
- impl: Migrated raw-entry, binary-entry, and direct-binary spawn handlers now
  derive their recipe mint parent from the live scheduled TCB through
  `KernelCallContext`; the legacy recipe seed remains restricted to the
  no-current-TCB kernel-bootstrap seam. A regression proves an empty parent
  cannot acquire the declared recipe grants. Focused IPC host tests and lint
  completed with no lane failure, but the deployed CLI is still bootstrap-seed
  diagnostic evidence, not a mission-critical release result.
- impl: `InitService` now consumes `ServiceManifest` at the lifecycle boundary.
  Broker acquisition is injected and fail-closed for declared requirements;
  all terminal/restart transitions revoke old handles, `on_restart()` clears
  the manifest, and only then can a fresh broker issue new handles. The unit
  spec proves fresh replacement plus dependency-ordered boot/shutdown. This is
  a runtime manager improvement, not evidence that `os_main` launches PID1.
- impl: Added the live-scheduler filesystem-exec registration seam and made
  `_handle_spawn_binary_state` consume it. Explicit context/recipe/image/
  priority/scheduler inputs now create the child in the supplied live scheduler
  with a CSpace minted from the same context. The regression proves both
  fail-closed non-root authorization and a recipe child in that scheduler.
  The compatibility fs-exec bootstrap-scheduler family remains an open PID1
  boot integration task.
- impl: Added the shared `kernel_call_context_from_task` adapter and a
  path-specific filesystem authority policy. FAT32 opens now distinguish
  FileRead/FileWrite/FileCreate requirements for their flags, and descriptor
  operations preserve the canonical opened path for live CSpace re-checks.
  Focused policy and descriptor tests pass with the bootstrap-seed CLI; direct
  ABI file handlers now fail closed even where the model dispatcher is bypassed.
  Generic legacy POSIX descriptor backends, per-task isolation mount views,
  and a live PID1 remain active criteria.
- impl: Direct file handlers now activate the caller's task-scoped descriptor
  table before lookup/allocation. Process exit clears the FAT32 task-keyed
  handle/path table after closing descriptors; a regression keeps a different
  task's same-number descriptor intact while proving the exiting task's records
  are gone. Focused FAT32 and syscall specs plus lint completed with only the
  bootstrap CLI's repository-wide deprecation warnings.
- critical-mode: The filesystem gate now requires a concrete token owned by
  the context task. A foreign token and non-kernel `CapabilitySet.full()` are
  rejected; task 0 remains the explicit bootstrap exception. The focused policy
  test passed with the bootstrap-seed CLI and remains diagnostic evidence only.
- impl: Scheduler task construction now retags a delegated CSpace to the actual
  child TaskId, preserving kind/generation/lineage/depth. This closes a defect
  exposed by the filesystem ownership gate, where a recipe child previously
  retained parent-owned tokens. The live fs-exec regression verifies every
  recipe token belongs to the returned PID.
- impl: Added `SPAWN_RECIPE_SERVICE_MANAGER` and `pid1_launch`: PID1 is built
  from `/system/service_manager.smf` into the supplied trap-owned scheduler
  with concrete narrow seed authority; RV64 `os_main` now installs the trap
  runtime and uses ring-3 handoff when that image is available. Focused host
  tests cover PID1 preparation. This is not a QEMU boot claim: search found no
  target-native service-manager build, so normal RV64 boot currently follows
  its recovery fallback and AC-4 remains active.
- impl: The RV64 PID1 handoff now closes the ambient-spawn window only after
  PID1 has been registered with its concrete CSpace and before its first
  ring-3 instruction. Focused proof confirms task 0 alone retains the
  kernel-origin compatibility exception while a non-root ambient spawn is
  denied. A manifest-authorized PID1 child-spawn ABI remains required before
  this can demonstrate managed service startup under QEMU.
- impl: Added an explicit managed-workload `SpawnSpec` scheduler seam. It
  requires a caller-owned, delegable `ProcessSpawn` token plus normal executable
  authority and rejects the full launch if any requested grant is unavailable;
  it never runs a child with a partial pouch. Recipe-based live registration
  now uses this seam. The remaining connection is a narrow userspace PID1
  manifest/spawn syscall that supplies only verified specs.
- impl: Added the frozen `WorkloadManifest` and `CompiledExecutionPolicy`
  contract shared by services, containers, and agents. The compiler rejects
  mismatched identity/image hashes, malformed grant labels, duplicate syscall
  filters, zero process/memory limits, and audited workloads without retained
  logs. It emits a typed SpawnSpec but does not mint authority; launch retains
  the live parent-CSpace intersection.
- impl: `InitService.register_workload()` now retains the compiled execution
  policy at the lifecycle boundary. Its typed launcher receives that same policy
  on first start and on automatic restart only after the old broker handles are
  revoked and fresh handles are acquired. The focused service spec proves both
  launches use the bound image hash and the restart replaces the grant. A live
  PID1-to-kernel policy handoff remains the required next connection.
- hardening: `CompiledExecutionPolicy` retains the typed `ImageSpec`, and
  `InitService` rejects a mutable `ServiceDef.binary` path that diverges from
  that binding before it can reacquire a grant or invoke a launcher. This is
  path-integrity protection only; verified artifact-byte digest enforcement is
  still an explicit loader/PID1 acceptance gap.
- impl: Explicit `SpawnSpec` fs-exec launches now bind each new task to a
  unique, immutable nonzero process-view domain before returning it. The
  scheduler refuses a conflicting rebind, and the launcher exits the child on
  unexpected bind failure so no runnable unbound child is exposed. Focused
  fs-exec evidence confirms the binding; VFS/PID/IPC/network gates that consume
  it remain active work.
- impl: Process list/info/signal/priority/scheduler-control now fail closed
  across different nonzero process-view domains. A nonkernel caller may see
  itself, same-domain tasks, or direct children so PID1 can supervise a
  separately isolated service. Focused syscall evidence proves both peer denial
  and parent-child control; typed process/job handles remain required to replace
  the structural parent exception.
- hardening: Fork no longer resets a managed workload to the unbound process
  view. The new task preserves the parent domain and restrictive isolation
  fields while receiving its distinct COW address-space identifier; scheduler
  evidence covers that inheritance together with its attenuated CSpace.
- impl: `SpawnSpec.budget` is now enforced as a direct-child admission limit
  in the explicit managed fs-exec path. Unreaped zombies remain charged and a
  second launch is denied before child CSpace minting once the bound is reached.
  This is deliberately only the live PID-count slice of ResourceDomain; all
  other hierarchical resource controllers remain active work.
- impl: TCBs now persist principal, job, CSpace, resource-domain, and audit
  bindings. `KernelCallContext` reads those fields directly instead of deriving
  placeholders from task ID/capability generation; focused evidence proves new
  task and fork semantics. Manifest-derived IDs need the pending PID1 policy
  transport, so scheduler defaults are not yet a complete policy registry.
- hardening: Managed SpawnSpecs with a nonempty image hash are now bound to
  exact `UserProcessImage.file_bytes` using canonical `blake3:<hex>` before
  CSpace minting. PID1 supplies the digest derived from its launch bytes, and
  focused fs-exec evidence proves mismatch denial. Empty hashes are retained
  solely for legacy named-recipe compatibility, not compiled workload policy;
  compilation now rejects noncanonical BLAKE3 image identifiers as well.
- impl: Both FAT32 writers now accept an authoritative
  `SIMPLEOS_PID1_BINARY`. The pure-Simple bake stages the canonical path; the
  QEMU `make_os_disk` writer validates the target ELF, wraps it as SMF, stages
  FAT alias `/SYS/SVCMGR.SMF`, and the VFS resolves the canonical
  `/system/service_manager.smf` request. `SIMPLEOS_REQUIRE_PID1=1` makes the
  QEMU route fail closed when no payload is supplied. This is a packaging
  contract, not an image-producer claim: a target-native service-manager build
  and QEMU boot trace remain required.
- impl: The scheduler now registers a successfully prepared PID1 as its
  reaper. Parent exit reparents direct children atomically before zombie
  retention; if the configured reaper exits, children fall back to task 0 and
  it becomes the future adoption target. A zombie cannot become reaper.
  Focused scheduler evidence proves both adopted-child reaping and fallback.
  This is P0 lifecycle plumbing, not evidence of a booted userspace service
  manager or QEMU supervision.
- hardening: The direct `execve` ABI path now derives `KernelCallContext` from
  the real persistent TCB binding rather than reconstructing legacy scalar
  metadata. Its focused execve regression remains green; this keeps direct and
  model-dispatched syscall authorization aligned.
- hardening: Explicit managed spawn now rejects a `KernelCallContext` whose
  task is not the live scheduler current task before budget admission or CSpace
  minting. Focused fs-exec evidence covers the mismatch denial and a valid live
  parent launch, preventing authority/accounting/tree-parent confusion.
- impl: Managed child creation now installs an immutable one-time TCB security
  binding with fresh principal/CSpace/job/resource/audit IDs and explicit
  parent job/resource lineage. Focused fs-exec and context evidence passes;
  job termination traverses that lineage. Stable non-PID-backed domain objects
  remain required for full hierarchy control.
- hardening: PID1 handoff now permanently forbids the legacy ambient
  `CapabilitySet.full()` path for every caller, including task 0. PID1 already
  has a concrete minted CSpace, so service creation must remain on the managed
  mint path. Focused PID1/fs-exec evidence proves task 0 receives deny-all
  ambient caps after this handoff; the legacy root-compatible seal remains only
  for older boot flows.
- tracking: `doc/08_tracking/bug/pid1_target_service_manager_missing_2026-08-11.md`
  owns the missing target-native PID1 executable, manifest/spawn ABI, and QEMU
  service lifecycle evidence. AC-4 remains active until that tracker closes.
- tracking: `doc/08_tracking/bug/callerless_vfs_executable_read_bypass_2026-08-11.md`
  owns the legacy global executable-read/PATH probe bypass and its caller-aware
  VFS migration. AC-5 remains active until cross-domain VFS evidence closes it.
- impl: Shell PATH resolution no longer reads global VFS to probe executable
  existence. It constructs names only and attempts each through the gated spawn
  seam, continuing solely after ordinary not-found. Focused shell evidence
  passes; the underlying legacy scalar spawn/VFS bridge remains active work.
- hardening: The raw executable-byte VFS helper is now explicitly boot-only
  (`fs_exec_read_boot_executable_bytes`) and PID1 is its sole consumer. Focused
  PID1/fs-exec evidence passes; broader caller-aware VFS operations remain open.
- impl: Added `managed_workload_launch`, the typed kernel PID1-to-managed-spawn
  adapter. It rechecks policy/image/spec agreement, parses trusted bytes, and
  delegates only to the explicit live CSpace path. Focused evidence proves a
  valid compiled policy creates a pledged isolated child and a post-compile
  image-binding mutation is denied. A target-native userspace ABI remains open.
- impl: `ResourceBudget.process_limit` now binds to the spawned managed
  workload's descendant admission limit rather than PID1's direct-service
  count; memory pages bind once into its isolation profile. Focused evidence
  proves the workload can create one permitted child and the next is denied.
  CPU, I/O, and network resource controllers remain active work.
- impl: Nonempty compiled syscall allowlists now bind once to managed TCBs,
  inherit through fork, and deny unlisted calls in both syscall dispatch paths
  before handler side effects. Focused syscall evidence proves allow/deny
  behavior. Workload compilation now rejects missing/empty filters, requiring
  explicit syscall surfaces for every typed workload.
- impl: The scheduler now provides trusted job-wide termination. It snapshots
  live members, exits each through normal cleanup/reparenting, preserves other
  jobs, and refuses kernel job 0. Focused scheduler evidence covers job
  isolation; typed job handles and a userspace control ABI remain open.
- hardening: Every scheduler exit now replaces its zombie TCB CSpace with
  pledged deny-all and advances capability generation before status retention.
  This covers signal/job termination paths without an IPC manager; normal
  syscall exit continues to revoke IPC records and descriptors as well.
- hardening: Job termination now reschedules CPU 0 if its current task was
  terminated, preventing a current-pointer zombie. Focused evidence proves a
  ready task from a different job becomes current; multi-CPU stop/IPI handling
  remains active scheduler work.
- hardening: The legacy scalar fs-exec recipe bridge now rejects all callers
  after PID1's permanent authority seal; it can no longer manufacture a
  recipe-shaped parent CSpace from a numeric caller. Shell name resolution
  remains pure, but a scheduled shell needs the pending context-bound spawn
  ABI. Focused seal and blob-route evidence passes.
- hardening: P0 C ABI process, fork/exec, and IPC shims now enter the
  stateful dispatcher and adopt its returned scheduler/IPC state. The
  dispatcher enforces the task's syscall filter and uses the live TCB CSpace
  for ProcessSpawn, FileExec, and IPC authority. Remaining file/network/device
  direct shims are tracked as an explicit whole-syscall enforcement gap.
- impl: Added `compile_agent_policy`, which bounds the shared
  `WorkloadManifest` authority request by an effective LLM profile's typed
  filesystem roots and ProcessSpawn bit, then returns the normal compiled
  execution policy with child/model/tool budgets. Network, secrets, UI, model,
  and device profile dimensions fail closed until typed broker capabilities
  exist; the adapter never manufactures a raw credential or ambient grant.
- hardening: Network and device C ABI shims now also use the common stateful
  dispatcher. The dispatcher checks a managed task's syscall filter plus
  `NetConnect`/`NetListen`/`NetRaw` or typed device CSpace authority before the
  leaf runs; `socket()` retains its compatibility allocation behind that gate.
  Focused empty-CSpace network/device denial evidence passes.
- hardening: Primary VFS ABI calls (`open/read/write/close/stat/mkdir/readdir/
  unlink`) now use the common dispatcher for syscall filtering, while their
  existing handlers retain concrete-path KernelCallContext checks. Descriptor
  evidence passes; extended/mount/control file ABI calls remain in the direct
  coverage tracker until they take the same filter transition.
- hardening: Extended VFS ABI calls with concrete-path or descriptor semantics
  (`rename/rmdir/chdir/ftruncate/lseek/getcwd`) now use the same filter gate.
  Empty-prefix compatibility checks were removed only where the handler already
  authorizes an exact path; mount and security-control calls remain explicit
  coverage work.
- hardening: Mount/unmount ABI calls now enter the common dispatcher and check
  the caller's live `SystemMount` capability before forwarding to VFS. Focused
  empty-CSpace mount denial passes. Pledge/unveil/capability-transfer retain
  their direct path because they require state-returning lifecycle handlers.
- hardening: Pledge, unveil, and compatibility capability transfer now have
  state-returning handlers and enter the common dispatcher. The ABI adopts the
  returned scheduler/IPC state, preventing silent loss of monotonic
  restrictions; capability transfer additionally requires live
  `SystemPrivilege`. Focused stateful security evidence passes.
