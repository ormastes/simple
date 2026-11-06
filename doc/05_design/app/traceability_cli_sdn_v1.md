# Traceability SDN structural command

Status: implementation in progress; command acceptance and broad verification unqualified. All 20 REQ-TRC / 40 AC-TRC / WP0–WP7 remain required. Dependencies are the reviewed strict/typed shared owners in PR #2959; release admission remains a separate unresolved gate.

The production main entry parses TraceCliOptionsV1 completely before capture. Default and explicit output are one canonical simple.trace.qualification summary v1 SDN document with one LF. Help is text. JSON, unknown options, malformed/missing values and unsupported scopes/formats return usage exit 2 with stderr and empty stdout. UTF-8, NUL, argument count, per-argument bytes and total argument bytes are checked before spawning or reading. Quiet preserves the document and suppresses progress regardless of flag order. Human progress uses the canonical stderr owner. CLI process status uses its exit facade.

TraceCaptureLimitsV1 / TraceCapturedInputsV1 / TraceCaptureIssueV1 and trace_capture_worktree_v1 own checked bounded worktree materialization. Selectors remain authored in the report; normalized repository-relative source/test/doc identities are retained in capture. Parent traversal/outside roots, missing inputs, unsupported selected files and observed symlinks are refused. Existing dirs must be observed real dirs before an empty enumeration can succeed. Supported files use no-follow bounded reads; every observed ancestor is checked separately. UTF-8 is validated before parsing exact captured contents.

A successful find argv call provides NUL-delimited paths. No shell command text is interpolated; relative roots are prefixed ./ and NUL is rejected in supplied arguments. The existing bounded native provider can retain child exit 0 on output truncation. Acceptance therefore requires status 0, empty stderr, byte length within cap, valid UTF-8 and complete nonempty NUL records with the expected relative-path framing. Its truncation marker adds bytes beyond its retained cap; its incomplete marker lacks terminal NUL. Filenames resembling marker text are legitimate and are not banned. Real provider overflow controls are required. Platforms lacking find produce explicit infrastructure failure; this is not proof of the remaining supported-platform contract.

Checked one-level enumeration distinguishes authorized configuration absence from unreadable/provider failures. Configuration/default policy, exact config digest and parsed semantic fields participate in identity; traceability_config_from_captured_text_v1 performs no reread. Files are sorted/deduplicated while selector order/provenance is retained. A streaming SHA-256 hashes canonical versioned header and each sorted path/length/exact-content-digest record, each LF-framed. The header includes cwd, scope, selectors, configuration/default policy and the capture/classifier/rule policy version. Both warning evaluation and rendering consume captured values without filesystem rereads.

Sequential no-follow checks and reads do not establish atomic repository coherence or descriptor-based confinement. The native reader protects only its final component; observed ancestor checks do not close replacement races. snapshot.complete means this materialization completed, not that Git/index/worktree coherence or admission was established. qualification remains incomplete at completed structural exit 0 or 1. Missing input/capture errors use incomplete snapshot/evaluation exit 2; evaluation/report-budget failures retain an already materialized snapshot but mark evaluation incomplete. Infrastructure reports contain a diagnostic reason. Full WP4 snapshot/lifecycle/admission and exact immutable receipt contracts remain open.

Captured file count/bytes, per-file bytes, enumeration bytes/entries/process count and capture checkpoints/process deadlines are bounded. In-process native reads are not preemptible; no hard whole-operation deadline is claimed. The legacy parser operates on bounded captured buffers. Before warning-producing helpers, analyze_virtual_files_bounded_v1 computes the reviewed bound B = 6F + 2L + I + T, counting files, four companion-link arrays, requirement/NFR identifiers and raw-test paths including duplicates. Remaining-budget arithmetic avoids overflow. Header/link/config paths have separate byte bounds. Rejecting the bound is incomplete evaluation, never a completed violation. The shared parsed analyzer retains all files and links; output cardinality must satisfy both B and the configured diagnostic cap. This does not qualify worst-case analysis time or RSS.

The typed summary owner validates producer output. Its effective 1 MiB cap includes LF. Arguments total at most 64 KiB, leaving space for an infrastructure summary if full diagnostic serialization refuses; no partial document is written. Diagnostics retain code, observed path identity, snapshot, rule/version, origin and repair. The legacy checker has no exact column, so span availability is false and coordinates zero. These lexical observed-path subjects are not claimed as the full extracted graph/declaration entities. Full extraction, qualification major 2 and other families remain required.

TDD baseline: after narrowing unrelated hub imports, the actual old production command constructed 53 modules without fallback. The native seven-case SSpec observed four failed scenarios, then the missing-option scenario started a full-repository scan and the 30-second harness timed out before completion. The incomplete run is retained as such; no seven-case RED summary is fabricated. Its verified orphan was terminated. This is a concrete option-validation/performance failure addressed before capture. Final command and resource/producer boundary tests are still pending.

## Final scoped status (2026-10-11)

Configuration reads are capped at1MiB, with <=4096 warning-root members, <=4KiB
per member and <=64KiB aggregate checked before manifest allocation. Public
options/limits/cwd are checked before attempt allocation. Early capture refusals
use reserved worktree-attempt:unavailable, complete=false, with no captured
identity claim. NUL records are scanned by byte offsets; exact selected-root
observation is required for unfiltered walks. These changes are source-reviewed.

The earlier CLI stage passed7/0; final capture controls remain6/1 after three
cycles (Unicode/NUL positive control). Final command construction succeeded;
full acceptance is not claimed. See traceability_cli_tdd_2026-10-11.md report.

## Fixture transport / actual provider evidence update

The prior6/1 positive control was malformed: nil-coalescing Result does not
extract a text payload. The corrected helper explicitly matches Ok and asserts
len1/bytes[0]. No original capped suite was rerun or retroactively validated.
New native fixture regression3/0 and actual provider legacy6/5 -> current6/0
qualify concrete worktree-provider properties. See the CLI TDD report for
source-stage boundaries, owned inputs and P2 oracle limitations. Direct Unicode
selection is proven; find transport of that filename remains open. All20REQ/40AC
remain required; no full runtime or protected admission PASS is claimed.

## Query entry and harness surface increment — 2026-11-06 (slice 1)

Scope statement: slice 1 ("P0 query usable on seed") changes **no module or
layer boundary, no data model, no graph schema and no SDN document shape**.
`std.common.traceability` stays the pure owner; app adapters keep snapshots,
processes and rendering. The increment adds one entry route, one harness knob
and one input-tolerance rule, each listed here so later slices align to it.

1. **Direct program entry for the query CLI.** `src/app/traceability/query_main.spl`
   exposes `fn main() -> i64` that forwards `get_cli_args()` to
   `run_trace_query_v1` and exits with its status. `<simple> run
   src/app/traceability/query_main.spl <args>` therefore has exactly the argv
   contract and exit codes of `simple trace <args>` (0 help/complete, 1
   rendered-but-unverified or `TRACE-QUERY-NOT-FOUND`, 2 error). Rationale: no
   admitted Stage4 CLI dispatches `trace`, and the Rust seed dispatches none of
   the pure-Simple commands; program-run is the delivery route on any binary
   that can `run`. The `simple trace` registration (command_registry) is
   unchanged and remains the eventual surface; `main` is additive. The
   traceability-check entry (`main.spl`) already follows this shape.

2. **Harness contract.** `trace_query_p0_spec` accepts
   `SIMPLE_TRACE_QUERY_TEST_COMMAND` -- a whitespace-split command prefix that
   already routes to the query entry (the spec appends only query args) -- as an
   alternative to `SIMPLE_TRACE_QUERY_TEST_BINARY` (`<binary> trace <args>`).
   Neither set is still an explicit failure; no fallback process result exists.
   `scripts/check/check-trace-query-p0.shs` is the single owner of the
   alternate-index fixture (`build/test-artifacts/trace_query_p0/index`, built
   with `git read-tree HEAD` + one `update-index --cacheinfo` of a modified
   declaration blob; never the real index or worktree) and exports
   `GIT_INDEX_FILE` only for the spec process.

3. **Declaration input tolerance.** Registered declaration files
   (`doc/08_tracking/trace/features/*.sdn`) may begin with `#` comment lines.
   This is satisfied in the shared SDN parser (`std.common.sdn.parser.parse`
   skips leading full-line comments before every top-level shape dispatch,
   matching what the block-mapping route already did), not in the trace codec;
   `decode_trace_declarations` and the `simple.trace.declarations/1` schema are
   unchanged.

4. **Snapshot adapter tiers (stated, not changed).** `worktree_preview` reads
   files in-process and runs on the interpreter. `git_commit` and `git_index`
   go through `OwnedProcessLease` (owned-process v3), which the Rust seed
   interpreter deliberately reports as unavailable (`rt_process_owned_v3_adapter_unavailable`);
   those two routes and the mislabeled-tree rejection verify only on a native
   runtime provider (self-hosted/native `bin/simple`). Specs that need them are
   therefore Phase-3 verification, not seed-fixable defects.

Next slices (reverse references: which specs cover a requirement, bug <->
file links) touch the query model (`TraceNodeQueryV1`/page result) and will
get their own increment in this document before code lands.
