<!-- codex-system-test -->
# Collection planner system test plan

Status: design draft. The user selected the full functional scope in
`doc/02_requirements/feature/collection_planner.md` and balanced targets in
`doc/02_requirements/nfr/collection_planner.md`. No collection-planner system
spec, generated manual, or passing full CLI runner exists yet. Existing unit
and DataFrame specs below are narrower evidence and do not close a system
requirement.

Executable home: `test/03_system/app/compiler/feature/collection_planner_spec.spl`.
Generated manual: `doc/06_spec/03_system/app/compiler/feature/collection_planner_spec.md`.

## Traceability and required scenarios

Each row needs at least three independent executable scenarios: the normal
behavior, a semantic edge, and a rejected or unsupported case. The system
spec must invoke production entrypoints and inspect observable results or
durable plan receipts. A source-shape assertion or canned helper result is
not acceptance evidence.

| REQ | Existing narrower evidence | Required system scenarios | Status |
|---|---|---|---|
| 001 | `test/03_system/feature/scilib/df_merge_spec.spl`, `df_groupby_spec.spl`, `df_value_counts_spec.spl`, `df_scalar_broadcast_spec.spl`; `doc/06_spec/03_system/feature/scilib/` mirrors exist but need freshness checks | Typed column round trip; signed zero/NaN/duplicate/missing edge; dtype mismatch rejected | Partial; generic typed column missing |
| 002 | None across all five engines | Map/filter/flat-map/any/all parity; captured closure and Dict collision parity; missing runtime symbol fails build | Missing |
| 003 | `test/01_unit/compiler/semantics/hir_perf_facts_spec.spl` exercises an in-memory registry | Production registry binding; duplicate/stale row rejected; backend symbol mismatch rejected | Partial; no production registry load |
| 004 | Numeric DataFrame specs above | Generic unique/group_by first-seen order; collision and fallback behavior; operation-count scaling | Partial; generic indexed algorithms missing |
| 005 | Text-only hash collection specs, if admitted, are narrower than generic-key parity | Integer/text/enum/tuple/symbol keys; collision/resize/removal; unsupported hash/equality rejected | Missing |
| 006 | `test/01_unit/compiler/semantics/hir_perf_facts_spec.spl` and existing `COLL` lint specs | Equivalent chain/loop warnings; bounded intentional work suppressed; strict-mode assumptions explained | Partial; no production typed equivalence |
| 007 | `test/01_unit/compiler/semantics/collection_plan_spec.spl` and `collection_plan_extractor_spec.spl` | Chain and loop extract equivalent DAGs; unknown facts block rewrite; malformed or cyclic plan rejected | Partial; no production invocation |
| 008 | None for emitted fused MIR | Pure map/filter parity and allocation count; callback/throw/mutation/short-circuit edge; unproven case uses original path | Missing |
| 009 | `test/01_unit/compiler/mir_opt/collection_plan_selection_spec.spl` is only an advisory chooser | Semi/anti/first/all/index candidate parity; duplicate/order/output-work edge; illegal candidate rejected with reason | Missing production lowering |
| 010 | In-memory `.sprof` work is provisional until wired to the compiler | Valid profile changes guarded choice; stale/mismatched profile ignored; missing profile preserves original behavior | Missing production adaptation |
| 011 | No system explain or differential evidence | Selected and rejected plan explanation; differential multi-engine oracle; selected NFR scaling/RSS gate | Missing |

Recently appearing untracked explain/profile files in the shared worktree are
treated as concurrent work until their owner completes and verifies them.
They are not counted as accepted evidence here.

## Environment and execution order

1. Use an admitted pure-Simple compiler and compiled SPipe runner. Interpreter
   mode alone loads `it` blocks without executing them. Keep the Rust seed and
   bootstrap-only diagnostic binaries out of release evidence.
2. Prove REQ-002 on the same deterministic fixtures in interpreter, JIT,
   LLVM AOT, self-hosted native, and bootstrap routes before enabling source
   lambda repair or synthesized Dict indexes. Capture command, exit status,
   output, runtime-symbol audit and artifact hashes for each route.
3. Cover typed columns, generic hash keys, standard-library order and
   complexity (REQ-001/004/005). Use fixed adversarial collision fixtures and
   NaN, signed-zero, duplicate and missing-value cases.
4. Cover registry, diagnostics and logical extraction (REQ-003/006/007).
   Capture the typed source span, resolved symbol, registry version, fact
   receipt, blockers and exact original HIR fallback.
5. Cover fusion and equality-key physical lowering (REQ-008/009). Compare
   results, callback count/order, exceptions, allocations and selected MIR
   against the unfused original on every supported backend.
6. Cover `.sprof`, explain output and selected NFR thresholds (REQ-010/011).
   Profiles must be tied to function, target, backend, registry and epoch;
   invalid profiles must not legalize a rewrite.

Fixtures must use deterministic seeds and bounded input sizes for ordinary
system runs. The scaling lane uses 1k, 2k, 4k and 8k indexed workloads with
bounded output multiplicity; its endpoint operation-count exponent must be at
most 1.15. Record all four counts and separate all-equal output costs. Compare
at least five warm runs per fixture against the same-revision unoptimized
baseline: at most 10% median wall-time, 20% median peak-RSS and 5% warm
compiler startup/request latency regression. Measure cold startup without a
numeric gate. Do not use elapsed time
alone as an algorithmic oracle. Fold backend/edge/stress matrices in the
generated manual while keeping primary scenario steps visible. Capture
text/exec/log/artifact evidence; no screenshot is needed for the explain TUI.

## Pass criteria and manual generation

All 33 minimum scenarios must contain real assertions and pass in compiled
mode; no `pass_todo`, tautological assertion, silent helper or fake receipt is
accepted. Every algorithm-changing rewrite needs differential and scaling
evidence. Run `simple spipe-docgen <spec> --output doc/06_spec --no-index` after
writing the spec; require `0 stubs`, review the mirrored Markdown, and confirm
no executable `.spl` remains under `doc/06_spec`. Run each acceptance criterion
once per session and stop after the repository's three verify/fix cycles.
