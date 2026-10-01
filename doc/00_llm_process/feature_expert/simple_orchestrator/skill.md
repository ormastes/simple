# Feature Expert — Simple Orchestrator / Simple Container / Simple CI orchestration

## Role

Own process knowledge for the SIMPLEORCH lane: a Simple-native container
orchestrator, one portable container-management core, small host-specific
runtime providers, and the CI orchestration built on top of them.

## Feature Links

- Research (design authority): [`doc/01_research/os/container/simple_orchestrator_and_container_2026-09-06.md`](../../../01_research/os/container/simple_orchestrator_and_container_2026-09-06.md)
- Lane state / milestone table: `.spipe/simple_orchestrator/state.md`
- Contract: `src/lib/common/contracts/orchestration/resource_v1.spl`
- Spec: `test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl`
- Generated manual: `doc/06_spec/01_unit/lib/common/contracts/orchestration/resource_v1_spec.md`
- Fixtures: `test/fixtures/orchestration/`
- Requirements / plan / design pages: not written yet — the research doc's
  ORCH-001..016 table, §15.2 milestones and §14 acceptance catalog stand in.

## Do not touch

`src/os/services/container/**` is owned by `container_live_wiring`,
`simpleos_harden_t3ctr_manager`, `simpleos_harden_t4oci_import` and
`process-isolation`. Research §8.4 requires parity fixtures before any
extraction. Extend `src/app/ci/` for the CI half; do not add a second scheduler.

## Current state

The CI application EXECUTES. `Pipeline` decodes and expands into ordered `Job`s;
`src/app/ci/pipeline_runner.spl` launches real host processes on the
`native-process` lane and writes nonce-verified receipts. 24 examples green — on
the RUST SEED only; nothing here is self-hosted evidence yet.

The `native-container` lane is BLOCKED on this host (docker socket group-denied;
`runc --rootless` dies on `kernel.apparmor_restrict_unprivileged_userns=1`).
TODO DB rows 275-277. A blocked container job is recorded BLOCKED and never
downgraded to a host process — that refusal is asserted in the spec.

**Corrected 2026-09-07:** an earlier revision of this file said M2+ was blocked
because `src/lib/nogc_async_mut/kernel_plugin/` is absent. The directory is
still absent, but it blocks only ORCH-015 (bounded no-GC async hot paths). A
synchronous Job/CI runner needs none of it, and one was built and run. Do not
repeat that inference.

## Verification commands

```bash
bin/simple test test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl --no-session-daemon
bin/simple spipe-docgen test/01_unit/lib/common/contracts/orchestration/resource_v1_spec.spl --output doc/06_spec --no-index   # require 0 stubs
sh scripts/check/lint-cached.shs src/lib/common/contracts/orchestration/resource_v1.spl
sh scripts/check-workspace-root-guard.shs audit --strict   # PRE-EXISTING RED (211, all tools/ + var/lib); this lane adds 0
```

Record binary identity with every run — `bin/simple` is a symlink other lanes
replace mid-session:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)" && bin/simple --version | head -2
```

## Traps found in this lane (2026-09-07)

- **`namespace` is a hard-rejected identifier.** A struct field, local, or field
  read named `namespace` is refused by the compiler's common-mistake check ("Use
  'mod' for modules instead of 'namespace'") — and it is NOT in
  `doc/07_guide/quick_reference/syntax_quick_reference.md`'s 124-keyword list.
  `ObjectMetaV1.ns` carries `metadata.namespace` because of this. Record:
  [`doc/08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md`](../../../08_tracking/bug/namespace_identifier_hard_rejected_2026-09-07.md).
- **An SDN value containing a colon must be quoted.** `image:
  registry.example/probe@sha256:aa` parses as a nested mapping, so a text decode
  rejects it on type. Correct parser behaviour; quote such values in fixtures.
- **The strict profile needed no new duplicate-key detector.**
  `parse_with_spans_and_issues` already returns `SdnIssue(kind:
  "duplicate_key", …)` with 1-based line/col, and its span map is keyed by the
  same dotted path the schema uses — so "any issue rejects" gives real source
  locations for free. Do not write a second detector.
- **`text.to_int()` fails open to 0 on garbage**, so quantity parsing uses a
  local digits-only converter that returns -1. Keep it that way; a rounded or
  zeroed quantity would be a placement decision made on a guess.

## Update Rule

Update this file whenever a milestone row in `.spipe/simple_orchestrator/state.md`
changes state, a new contract or provider lands, or a trap above is fixed.

## Slice-2 surfaces (2026-09-07)

- CI contract: `src/lib/common/contracts/orchestration/ci_v1.spl` (`Job`,
  `Pipeline`, `expand_pipeline`)
- CI runner: `src/app/ci/pipeline_runner.spl` (`probe_linux_oci`, `run_pipeline`,
  `JobReceiptV1`, `RunReceiptV1`)
- Specs: `test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl`,
  `test/02_integration/app/ci/pipeline_runner_spec.spl`,
  `test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl`
- Blocked-lane row:
  `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md`

```bash
bin/simple test test/01_unit/lib/common/contracts/orchestration/ci_v1_spec.spl --no-session-daemon
bin/simple test test/02_integration/app/ci/pipeline_runner_spec.spl --no-session-daemon
bin/simple test test/01_unit/lib/common/sdn/sdn_sequence_duplicate_key_spec.spl --no-session-daemon
```

## More traps found (2026-09-07)

- **SDN block-sequence entries were reported as duplicate keys.** `- name: a` /
  `- name: b` produced `duplicate_key @ spec.jobs.- name` — note the glued `- `
  marker, which is the tell. Every strict consumer therefore refused any
  multi-entry sequence. Fixed in `_sdn_issue_block`; record:
  [`sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md`](../../../08_tracking/bug/sdn_block_sequence_entries_reported_as_duplicate_keys_2026-09-07.md).
- **`simple lint` can abort, and the verdict still says "1 with findings".**
  `error: semantic: class CodeLine has no field named code` depends on the linted
  file's import closure, not its content — a 4-line file that only imports
  `ci_v1` aborts while `ci_v1` itself lints clean. Do not record that as a
  quality failure against the file. Record:
  [`lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md`](../../../08_tracking/bug/lint_codeline_has_no_field_code_closure_dependent_2026-09-07.md).
- **An ordering oracle whose fixture is already in topological order is
  vacuous.** The first diamond fixture declared jobs in dependency order, so
  deleting the dependency edges did not change the result. Any ordering test
  needs a fixture whose declaration order is NOT a valid execution order.
- **`unshare -U` succeeds here while `unshare -Ur` and nested namespaces fail.**
  Probing "can I make a user namespace" says yes and is useless; probe the
  operation runc actually performs (`unshare --user --mount true`).
