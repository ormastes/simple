# Feature: SimpleOS Production Host Master Plan (Convergence + Enforcement)

## Raw Request
/goal with spipe dev skill, do complete simpleos production host master plan.md
(master plan saved at doc/01_research/domain/simpleos_production_host_master_plan.md;
parallel execution plan at doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md)

## Task Type
feature (multi-lane umbrella; Stage S serial + Stage P parallel lanes)

## Refined Goal
Drive the SimpleOS production convergence program: land Stage S (shared truth
ledger + frozen ABI v1 contract + duplicate-owner guard), then execute Stage P
lanes (P1 IPC, P2 process/loader, P3 VFS unify, P4 services/TTY, P5 POSIX
truth, P6 toolchain lld, P7 std.config, P8 LLM profiles) with disjoint file
ownership per lane.

## Acceptance Criteria
- AC-S1: `doc/08_tracking/os/production_status.sdn` names one canonical owner
  and maturity for every core OS subsystem; guard spec asserts ledger/code parity.
- AC-S2: `src/os/kernel/abi/abi_v1.spl` freezes ABI v1 by REFERENCE to the
  existing canonical type owners (`os.kernel.types.*`, `cspace_spawn.SpawnSpec`)
  — no parallel type layer (master plan §4 non-negotiable applied to itself).
- AC-S3: `test/01_unit/os/arch/duplicate_owner_spec.spl` fails closed on
  duplicate-suffix trees (`*_v2.spl`, `new_vfs`, `fast_loader2`) and on
  ledger/owner drift; runs green via single-file `bin/simple test`.
- AC-S5: ABI RFC template exists at `doc/04_architecture/os/abi/rfc_template.md`.
- AC-P*: each Stage P lane records its own state under
  `.spipe/simpleos_harden_p<N>_*/state.md`, touches only its exclusive paths,
  and leaves a runnable spec + evidence note. Lane gates per plan doc.

## Scope Notes / Decisions
- 2026-07-27: S2 revised from "7 new *_v1.spl type files" to ONE contract index
  file. Reason: `os.kernel.types/` (14 modules) + `cspace_spawn.SpawnSpec` +
  `capability_types` rights bits ALREADY own these types; creating parallel
  structs would violate the plan's own no-second-envelope rule and the
  export-use-hub dependency rule. Plan doc updated to match.
- S4 (evidence fail-closed helper) folded into the guard spec as local helpers
  until a second consumer exists (ponytail: no abstraction with one consumer).
  Deletion condition recorded in plan doc.
- runtime_need: none — Stage S uses only `app.io.mod` facades in specs; no new
  rt_* externs (avoids bootstrap-rebuild wall). facade_checked: app.io.mod
  (file_exists/file_read_text/shell_lines). chosen_path: reuse-facade.
  rejected_shortcuts: raw `extern fn rt_*` in spec (raw_rt_access lint);
  export-use ABI hub (dependency hygiene).

## Stage Status
- Stage S: DONE (guard green, re-verified post-lanes: 4+1 examples 0 failures).
- Stage P: ALL 8 LANES GREEN (first increments). Verdicts below.

## Stage P results (2026-07-27)
- P1 IPC: 12 ex/0 fail. Single-use guard (`SingleUseLedger`) added to
  cspace_spawn.spl (was doc-only advisory flag); l4_fast_ipc marked honest
  model. No reply-object on syscall path yet. Real gate (2-proc QEMU
  call/reply) NOT met — transfer algebra only.
- P2 loader: 11 ex/0 fail. Root-only ambient-spawn guard (spawn_authority.spl)
  wired at fs_exec bridge. 3 ambient sites remain in P1-owned
  syscall_process.spl (143/660/729); boot seal `spawn_authority_seal_bootstrap()`
  has no caller yet — guard permissive until armed.
- P3 VFS: 7 ex/0 fail. vfs_handle_table.spl fixes handle→mount association
  (was mount[0] routing). UNWIRED: real VFS is src/os/services/vfs/** (plan
  updated to extend P3 ownership; increment 2). Stack inventory: 3 overlapping
  FS stacks + 4th FAT32 copy recorded.
- P4 TTY: 4 ex/0 fail. tty_write now delivers bytes to drainable OutputBuf
  (was accepted-count-only). PTY round-trip deferred (needs endpoint routing).
- P5 POSIX: 6 ex/0 fail. Honest profile matrix at doc/02_requirements/os/
  posix_profiles.md (20 impl/5 partial/9 stub/6 absent). Fixed dishonest guest
  mmap() (silent MAP_SHARED downgrade → EOPNOTSUPP). flock()-always-0 deferred.
- P6 toolchain: gate authored + verified fail-closed (NOT executed). Finding:
  ld.lld NOT staged in any guest image; lld_static never built. Ordered
  blockers + resume cmd `sh scripts/os/ssh_lld_link_uefi.shs` recorded.
- P7 config: 31 ex/0 fail. std.config core extracted to src/lib/common/
  config_core/ (schema+layers, 10-layer precedence w/ mandatory-as-ceiling).
  IDE call-site swap = increment 2 (8-step resume plan).
- P8 LLM: 18 ex/0 fail. profile_registry.spl w/ §17 deny-wins intersection +
  6 built-in profiles. SpawnSpec wiring = next increment.

## Bugs filed centrally (found by lanes, outside any lane path)
- lint_class_receiver_get_str_traceability (P1+P3): lint dies on any file with
  a `class`. HIGH — blocked lint as a lane gate.
- selfhost_two_hop_field_method_mutation_lost (P4): mutation via 2 struct-field
  hops from self silently lost on self-hosted binary. HIGH, systemic for ECS.
- parser_bare_trailing_neg_literal_folds_prev_line (P7): bare `-1` line folds
  into previous line, silent wrong value. HIGH.
- lint_coll006_concat_loop_false_positive_negative (P7): COLL006 false +/−.

## Cross-lane hand-offs for next tranche
- P2 boot seal must be armed by the boot owner (not a P2 path).
- P2's 3 remaining ambient sites live in P1's syscall_process.spl.
- P8 resolve_effective + P2 spawn_spec_effective_rights must meet at spawn time.
- P3 increment 2 extends into src/os/services/vfs/**.

## Evidence
- 2026-07-27 Stage S gate: `<scratch>/bin/wjob run test/01_unit/os/arch/duplicate_owner_spec.spl`
  → "4 examples, 0 failures" + calibration "1 example, 0 failures", RC=0.
  Binary: copy of bin/release/x86_64-unknown-linux-gnu/simple (SEED — deployed
  bin/simple is a stale seed w/ banner; single-file `simple test` hung >300s
  twice (known seed init-hang class), run-lane verdict used per spipe skill).
  Landmine hit + fixed: `@step "..."` fn annotation rejected by parser — use
  plain step() calls only (matches documented docgen gotcha).
- Stage P: 8 lane agents launched 2026-07-27 (disjoint paths, no-commit rule).
