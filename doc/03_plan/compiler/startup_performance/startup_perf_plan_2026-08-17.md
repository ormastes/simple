# Startup Performance Implementation Plan (2026-08-17)

**Source research:** `doc/01_research/compiler/startup_performance/startup_perf_architecture_2026-08-17.md`
(sections 0, 5, 6, 14, 15). This plan phases the five requested tracks:
(a) `load_policy` replaces public mmap policy, (b) config-driven dynamic-lib
loading on presence/placement/activation axes, (c) dynamic CLI arg addition
without a core rebuild, (d) compiler/loader/interpreter optimization with
profiling, (e) coupling/cohesion measurement gates.

**Global rules (apply to every phase):**
- Evidence: acceptance is met only by an explicit `Results:` line with a
  non-zero checked/scenario count in test output (SPipe convention). Exit 0
  alone is NEVER a pass; a run with no result line is `INCONCLUSIVE` and
  requires a direct `bin/simple run` reproduction.
- Verification tiers: **T0** = targeted probe (`bin/simple run` a focused
  fixture or one `*_spec.spl`, seconds-to-minutes); **T1** = affected spec
  subtree via `bin/simple test <dir>`; **T2** = full `bin/simple test`;
  **T3** = `bin/simple build bootstrap`. Always start at T0; escalate only
  when a phase touches the compiler binary or codec files. Never default to
  full bootstrap.
- Record binary identity with every timing:
  `readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"`.
- No new cache root; extend the existing CAS/semantic cache per research §10.
- All new code in `.spl`/`.shs`; no inheritance; generics use `<>`.

---

## Phase A — `load_policy` enum replaces public mmap policy

**Goal.** Public launch metadata and startup plan express *intent*
(`load_policy: normal | index_only | map_selected_segments |
read_ahead_selected | direct_exec | auto`), and `mmap` / `pread` / read /
VFS-prewarm / cached-image mapping become loader *provider strategies*
(research §1.3, §6.10). Back-compat: `mmap_hint`, `include_mmap_cache`, and
cache strategy `mmap` remain readable aliases mapped to
`map_selected_segments` with a deprecation receipt; no existing artifact or
config breaks.

**Owned files.**
- `src/app/startup/launch_metadata.spl` — add `load_policy` field + alias
  decoding (single owner; hot file).
- `src/compiler/80.driver/driver_aot_smf_output.spl`,
  `driver_aot_native_output.spl` — emit `load_policy`, keep alias emission
  behind a compat flag for one release.
- New `src/app/startup/load_policy.spl` — enum, alias mapping, strategy
  selection port (provider chooses mmap/pread/read per policy + size
  threshold).
- Specs: new `test/01_unit/app/startup/load_policy_spec.spl`.

**Steps.**
1. A1: define enum + codec with golden vectors (old images with only
   `mmap_hint` decode to `auto`/`map_selected_segments`; new images
   round-trip; unknown value fails closed).
2. A2: thread `load_policy` through `StartupPlanV1`-equivalent structs in
   the current launch path; providers translate policy → mechanism.
3. A3: deprecation receipt when an alias is used; no removal this phase.

**Acceptance.**
- T0 probe: `bin/simple run` a fixture that loads one SMF under each policy
  and prints the chosen mechanism; output must contain
  `Results: N policies checked, N mapped` with N ≥ 5.
- `load_policy_spec.spl` passes with explicit scenario count (`Results:` line).
- Alias back-compat: decoding a pre-change metadata blob yields identical
  load behavior; spec asserts byte-equal plan hash for the alias vs the
  mapped policy.
- Grep gate: no NEW public field named `mmap*` outside the alias shim
  (`/usr/bin/grep -rn "mmap_hint\|include_mmap_cache" src/ | wc -l` does not
  grow; count recorded in handoff).

**Verification tier.** T0 → T1 (`test/01_unit/app/startup/`). T2 only if
codec structs shared with the driver change shape. No bootstrap needed —
stdlib/app source is read fresh every run.

**Rollback.** Enum decoding is additive; revert = drop `load_policy.spl` and
the new field reads (aliases were never removed). Single-commit revert, no
artifact migration.

---

## Phase B — Config-driven dynamic-lib loading (presence/placement/activation)

**Goal.** SCI/SDN configuration selects which modules load dynamically —
aspect dynload, loader dynload, optimizer dynload — via three independent
axes (research §0, §5.1–5.4):

```text
capability: off | auto | on          # does it exist
placement:  auto | static | dynamic  # static or external artifact
activation: startup | command | first_use | hotspot | manual
```

`placement=auto` folds static on full rebuild when embedded impl hash ==
configured hash; `placement=dynamic` stays external forever (§5.2–5.3).

**Owned files.**
- New `src/lib/common/structural/component/` — `ComponentDescriptorV1`,
  resolution enums, `resolve_component` (research §5.1/§5.3), goldens.
- `src/lib/nogc_sync_mut/composition/codec.spl` + `cli_registry.spl` —
  descriptor section in SCI (ONE owner; see parallel plan WP-19s).
- New `src/app/startup/component_resolver.spl` — static-table lookup +
  dynamic admission (path, digest, ABI, interface hash, capability policy).
- Config surface: `simple.sdn`-style `components:` block compiled by the SCI
  generator; stage-0/startup never parses SDN on the hot path.
- Wiring targets, one adapter each: optimizer plugin registry
  (dynload optimizer), loader capability modules (dynload loader
  capabilities), aspect pack activation (dynload aspects).

**Steps.**
1. B1: contract + resolver with golden vectors (stale-static picks dynamic;
   matching hash picks static; `dynamic` never folds; `off` = ABSENT with no
   registration residue).
2. B2: SCI descriptor section + generator; config-only edit compiles 0
   modules, links 0 objects.
3. B3: wire optimizer dynload first (existing plugin registry is closest to
   working), then loader capabilities, then one aspect pack (log.debug).

**Acceptance.**
- Resolver spec: `Results: 12 resolution scenarios, 12 passed` (or actual
  count) covering the §5.3 decision table.
- Optimizer proof (from WP-55): modify optimizer source, rebuild ONLY
  `optimizer.smf`, run compile — transformed output proves the dynamic body
  executed, with `Results:` naming the artifact digest; then full rebuild
  and the same run shows `resolution=STATIC` with no `.smf` open (strace or
  load receipt as evidence).
- Absence proof: `capability=off` build's binary/link map contains no
  symbol/string for the disabled component (grep on `nm`/map output,
  count printed in a `Results:` line).
- Sabotage: corrupt the dynamic artifact digest in SCI → admission must
  FAIL with an explicit error, never silently fall back to static.

**Verification tier.** T0 per resolver scenario; T1 on
`test/01_unit/lib/composition/` (or created equivalent); T3 (bootstrap) only
for B3's fold-on-full-rebuild proof — that claim is *about* rebuild, so one
bootstrap run is the probe, not the default loop.

**Rollback.** Adapters are additive behind descriptor lookup; default SCI
ships every current component as `on/static/command`, byte-identical
behavior. Revert = regenerate SCI without the descriptor section (old reader
ignores unknown sections until the feature bit is set; do not set the bit
until B3 lands).

---

## Phase C — Dynamic CLI arg addition without core rebuild

**Goal.** Adding/renaming a command, exact option, alias, help line, value
map, or `--x<ns>-<key>[=<val>]` extension namespace regenerates SCI only —
zero compiled modules, zero links, `simple-core` digest unchanged
(research §5.7–5.13, §14 WP-19/19a/19b/19c).

**Owned files.**
- `src/lib/nogc_sync_mut/composition/{codec.spl, cli_registry.spl,
  cli_command_wire.spl}` — `SCI_SECTION_CLI_OPTION_ROUTE_V1`,
  `SimpleCliOptionRouteRecordV1`, `SimpleCliExtensionNamespaceRecordV1`,
  `StartupPlanPatchV1` (ONE owner, serialized with Phase B's codec work).
- New `src/app/startup/option_router.spl` — bounded exact-option lookup,
  plan-patch application, `--x` lexical split
  (`--x[a-z][a-z0-9_]{0,31}-key[=value]`, `=`-only values, hard `--`
  boundary, `after_entry` windows). No provider load during argv parsing.
- New `src/lib/nogc_sync_mut/composition/cli_extension_wire.spl` —
  `SimpleCliExtensionV1` (describe/validate/apply/complete), pointer-free
  bounded batches.
- Help/completion generator (new, no codec edits): SCI option/help index;
  root help stays I/O-free.
- `src/app/cli/_CliMain/*` untouched except by the designated integration
  owner at cutover (parallel plan).

**Steps.** C1 records+codec (fail-closed feature bit: old reader rejects an
option-requiring image rather than ignoring options) → C2 router → C3 wire +
one real provider namespace (`--xlog-level=debug` binding to the Phase B
aspect pack) → C4 help/completion + migration report of currently hardcoded
options.

**Acceptance.**
- Zero-rebuild proof: edit a `cli_options:` config record, regenerate SCI,
  and show `compiled modules: 0, linked objects: 0` in generator output
  plus unchanged `sha256sum` of the core binary — both echoed in a
  `Results:` line.
- Grammar corpus spec: namespace/key/value shapes, malformed forms,
  `--` boundary, unknown namespace = error, missing optional provider
  honors `warn_skip`; `Results: N tokens classified` with the corpus size.
- Sabotage (WP-19a): place a marker artifact as an unrelated provider; parse
  argv containing only exact options — the marker file must remain unopened
  (probe checks open() evidence).
- Router purity: no heap allocation / provider activation during parsing on
  the probe path (link-map/receipt evidence, counts in `Results:`).

**Verification tier.** T0 grammar probes; T1 composition + startup unit
specs; T2 once before declaring the phase done (codec files are shared with
every provider). Bootstrap only at cutover (integration owner's gate).

**Rollback.** Feature bit gating: until the bit is set in shipped SCI, the
old router path is authoritative. Revert = regenerate SCI without the
option section. Codec additions are append-only sections; never edit
existing record layouts in place.

---

## Phase D — Compiler / loader / interpreter optimization with profiling

**Goal.** Measured wins on the research lanes: startup route cost, loader
segment path, interpreter steady state, compiler warm/incremental — each
change admitted only with before/after profiles (research §8–§10, §12).

**Owned files.**
- New `test/05_perf/startup/` harness lanes: root help/version, source
  cold/warm, SMF load, one-body-change compile. Immutable manifest per run
  (binary digest, host, load, sample count, p50/p95, RSS, opens, maps).
- Loader: segment-oriented load path modules (per research §8) behind the
  Phase B loader-capability descriptors; per-symbol executable-buffer
  allocation removed from the normal path.
- Interpreter: profiling first — instrument the existing MIR interpreter
  dispatch (level-gated logs, default off) to find top opcodes; only then
  targeted fixes (dispatch, frame layout). ExecIR itself is OUT of scope for
  this plan (research Phase 5); do not mutate the reference interpreter
  semantics.
- Compiler: warm no-op and one-body-change lanes over the existing CAS;
  wire `interface_digest_of` (`action_key.spl:197-204`, currently ZERO
  callers) into the cache key as the first concrete incremental step, and
  verify `SmfManifest` on load.

**Acceptance.**
- Every optimization lands with a perf report: ≥ 5 samples, p50/p95, binary
  identity, and a `Results: lane=<x> before_p50=<a> after_p50=<b>` line.
  One-run timings are historical notes, never admission evidence.
- No regression: touched lanes within ±5% or the change carries a filed
  bug/todo per CLAUDE.md's perf rule.
- Loader: O(segments) mappings on the probe fixture, zero RWX, evidence =
  `/proc/self/maps` dump counted in the spec.
- Interface-digest wiring: body-only edit of an imported module hits cache
  for importers; interface edit invalidates them — both proven by cache
  hit/miss receipts with counts.

**Verification tier.** T0 perf probes (single fixture, strace/maps); T1 for
correctness parity of touched interpreter/loader paths; T3 once for the
compiler-lane claims (they are about rebuild behavior).

**Rollback.** Each optimization is descriptor-gated (Phase B placement) or
flag-gated; the reference interpreter path is never modified, so parity
revert = select reference provider.

---

## Phase E — Coupling/cohesion measurement as before/after gates

**Goal.** `bin/simple deps fast` / `bin/simple deps normal` (closure
metrics) run before Phase A and after each phase; import-closure size,
fan-in/fan-out, and root-closure module count are the objective
coupling/cohesion measure that the stripping phases must move.

**Owned files.**
- `src/app/cli/dispatch/table.spl` + new `src/app/deps/` command module if
  `deps` is not yet a command (verify first; if an equivalent exists under
  `simple_dependencies`/info tooling, extend it instead of adding a
  duplicate — never build a second metrics root).
- Baseline snapshots under `doc/10_metrics/startup_perf/` (auto-generated
  dir rules apply).

**Metrics.** per root route: modules in closure, edges, max fan-out,
aspect-implementation imports from core (target 0 after Phase B/C),
`_CliMain` fan-in.

**Acceptance.**
- `bin/simple deps fast` completes < 5 s warm and prints
  `Results: N modules, E edges` (non-vacuous: N > 0 mandatory).
- Recorded before/after table per phase; Phase B/C must show the root
  closure shrinking or hold steady with a filed explanation.
- Spec compares two committed snapshots and fails on unexplained growth
  beyond a configured band.

**Verification tier.** T0 (the tool run IS the probe); T1 for its spec.

**Rollback.** Pure tooling; revert freely. Snapshots are append-only.

---

## Phase ordering and gates

```text
E(baseline) -> A -> B -> C -> D -> E(re-measure, per phase)
```

A is independent and lands first (small, alias-safe). B blocks C's provider
binding and D's descriptor gating. E brackets everything. Each phase exits
through its acceptance list; the parallel-agent breakdown and higher-model
review gate live in
`doc/03_plan/agent_tasks/startup_perf_parallel_plan_2026-08-17.md`.
