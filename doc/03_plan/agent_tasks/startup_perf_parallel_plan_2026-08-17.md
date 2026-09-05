# Startup Perf — Parallel Agent Work Packages (2026-08-17)

Mirrors Wave 0/1 (WP-00..WP-19c) of
`doc/01_research/compiler/startup_performance/startup_perf_architecture_2026-08-17.md`
§14, scoped to what is feasible NOW in this repo. Companion phased plan:
`doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`.

## Ground rules (from research §14.1, binding)

1. Contracts freeze before implementation; no lane invents its own IDs,
   plan structs, SCI sections, or option grammar.
2. **One file owner per package.** Shared hot files have ONE serial owner.
3. Immutable baselines: every WP records starting SHA, integration SHA,
   `bin/simple` digest (`readlink -f bin/simple` + sha256), SCI schema
   version.
4. Every lane carries a **sabotage probe**; source-shape checks alone are
   `UNVERIFIED` until a live path executes.
5. No placeholder success: hollow artifacts, stubs, stale binaries, and
   exit-0-without-`Results:`-line are rejected.
6. Integration is per-file three-way merge; never whole-file overwrite of a
   hot file (see `.claude/rules/vcs.md` anti-revert protocol).
7. **Higher-model review gate:** no WP's done-mark is accepted from the
   implementing agent itself. See "Review gate" below.

## Do-not-touch shared hot files

| Path | Owner |
|---|---|
| `src/app/cli/_CliMain/*` (`main_and_help.spl`, `args_and_os_commands.spl`) | integration owner ONLY, at cutover |
| `src/app/cli/dispatch/table.spl` | integration owner (WP-E gets a reviewed one-line hook via the owner) |
| `src/lib/nogc_sync_mut/composition/{codec.spl, cli_registry.spl, cli_command_wire.spl, cli_provider_wire.spl}` | WP-19s owner ONLY (composition codec = one owner) |
| `src/app/startup/launch_metadata.spl` | WP-A owner ONLY |
| `src/compiler/80.driver/driver_aot_*_output.spl` | WP-A owner ONLY |
| root `__init__.spl` files of touched trees | integration owner |

Everyone else adds NEW modules/adapters beside these files.

## Wave 0 — census and contracts (all runnable now, read-mostly)

### WP-00s baseline-census
- **Owns:** new tracking/report files only; no code.
- **Tasks:** inventory existing startup plan / launch metadata / SCI-provider
  / SMF loader / dynSMF / optimizer plugin / AOP / cache-key / receipt names;
  duplicates + authoritative owners; capture root help/version + source +
  SMF strace traces; record binary digests; run `bin/simple deps` baseline
  (Phase E of the phased plan).
- **Acceptance:** census file with collision check for every proposed public
  name; `Results: N names checked, K collisions` line.
- **Sabotage:** point trace harness at the Rust seed binary; harness must
  refuse (provenance check via `--version`).

### WP-01s composition-contract
- **Owns:** new `src/lib/common/structural/component/**` + spec.
- **Tasks:** freeze `ComponentDescriptorV1`, presence/placement/activation
  enums, `resolve_component` (research §5.1/§5.3).
- **Acceptance:** golden vectors; stale-static and dynamic-always cases;
  `Results:` scenario count. **Sabotage:** flip one impl-hash byte in a
  golden vector → resolver must select dynamic admission, not static.

### WP-02s startup-contract
- **Owns:** new `src/app/startup/contract/**`.
- **Tasks:** freeze `StartupRequestV1`, `StartupPlanV1` (incl. `load_policy`
  from phased-plan Phase A), compact SCI header/route entries, plan hash.
- **Acceptance:** malformed/truncated/overflow vectors fail closed.
- **Sabotage:** truncate SCI header mid-field → bounded reader errors, never
  reads past `header_size`.

### WP-08s cli-option-contract
- **Owns:** new schema docs + golden vectors only; NO production codec edits.
- **Tasks:** freeze `SimpleCliOptionRouteRecordV1`,
  `SimpleCliExtensionNamespaceRecordV1`, `StartupPlanPatchV1`, `--x` grammar
  (`=`-only values, `--` boundary, fail-closed unknown namespace).
- **Gate:** every Wave-1 CLI agent imports these; nobody invents a prefix.

**Wave 0 exit:** one contract integrator confirms no duplicate ownership,
acyclic dependency graph, and that each Wave-1 WP can proceed without
editing another WP's contract. No implementation starts before this gate.

## Wave 1 — implementation (parallel after Wave 0 gate)

| WP | Agent | Owns (exclusive) | Depends |
|---|---|---|---|
| WP-A | load-policy | `load_policy.spl` (new), `launch_metadata.spl`, `driver_aot_*_output.spl` | WP-02s |
| WP-11s | stage0-classifier | new `src/app/startup/stage0/classifier.spl` + specs | WP-02s |
| WP-12s | sci-generator | build-side SCI generator (new files) | WP-01s, WP-02s |
| WP-13s | sci-reader | new bounded SCI reader + format tests | WP-12s goldens |
| WP-14s | static-component-table | build generator + generated table module | WP-01s |
| WP-15s | startup-planner | new planner module, no host I/O | WP-11s..14s |
| WP-19s | sci-option-route | **composition codec files** + option-route index modules | WP-08s, WP-12s |
| WP-19a-s | stage0-option-router | new `option_router.spl` + batch arena + specs | WP-11s, WP-13s, WP-19s |
| WP-19b-s | cli-extension-wire | new `cli_extension_wire.spl` + provider adapter | WP-08s |
| WP-19c-s | cli-option-help | new help/completion generator + migration report | WP-19s |
| WP-55s | optimizer-dynload | optimizer plugin registry + dynamic invocation adapter | WP-01s, WP-14s |
| WP-E | deps-metrics | new `src/app/deps/` (or extend existing dependency tool) + metrics snapshots | none |

Per-WP acceptance/sabotage follows research §14.4 verbatim, with these
repo-scoped notes:
- WP-19a-s sabotage: unrelated-option parse leaves a provider marker
  artifact unopened (open-evidence probe).
- WP-13s sabotage: valid route after an unselected corrupt record — indexed
  access must succeed without scanning the corrupt record.
- WP-55s acceptance: optimizer edit + `optimizer.smf`-only rebuild changes
  compile output (transformation visible); full rebuild folds static.
- WP-E acceptance: `Results: N modules, E edges`, N > 0; committed baseline
  snapshot before any Wave-1 merge.

**Wave 1 integration owner** (single agent, serial): `_CliMain/*`,
`dispatch/table.spl`, root `__init__.spl` cutover; connects planner +
option router; keeps old CLI path authoritative behind the SCI feature bit.

## Agent work brief template (copy per WP — research §14.10)

```text
Work package:
Baseline SHA:
Fetched integration SHA:
Owned paths:
Read-only dependencies:
Frozen schema versions:
Do-not-touch paths:
Required implementation:
Required unit tests:
Required integration/system tests:
Required sabotage probe:
Required cross-mode parity:
Required performance/evidence fields:
Known blockers/unsupported targets:
Memory/parallelism budget:
Handoff artifacts:
```

## Agent handoff template (research §14.11)

```text
RESULT: implemented | partial | blocked
BASE_SHA:
HEAD_SHA:
FILES_CHANGED:
PUBLIC_CONTRACT_CHANGES: none | versioned details
TEST_COMMANDS:
EXPLICIT_RESULT_LINES:
DIRECT_RUN_REPRO:
SABOTAGE_PROBE:
ARTIFACT_DIGESTS:
PERF_REPORT:
STATIC/DYNAMIC_PARITY:
REFERENCE/FAST/JIT_PARITY:
KNOWN_FAILURES:
INTEGRATION_NOTES:
```

A handoff with exit code only and no explicit result line is rejected.

## Review gate before accepting done marks

1. Implementing agent submits the handoff above; `RESULT: implemented`
   is a CLAIM, not a state change.
2. A **higher-model reviewer** (Opus-class or the designated certifier
   agent, never the implementing model/session) re-runs: (i) the stated
   `TEST_COMMANDS` verifying each `Results:` line is present and non-vacuous,
   (ii) the sabotage probe (must FAIL when sabotaged, PASS when restored),
   (iii) a diff review of owned vs actually-changed paths — any touch of a
   do-not-touch file is an automatic reject.
3. Only the reviewer flips the WP to done in this file's status table;
   implementation agents do not self-declare completion (research §14.1
   rule 10). Disputes escalate to the contract integrator, resolved by a
   schema version bump, never a silent contract edit.

## Status table

| WP | Status | Reviewer | Evidence link |
|---|---|---|---|
| WP-00s..WP-E | not-started | — | — |
