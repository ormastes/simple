<!-- codex-design -->
# Agent Task Plan — Simple Compiler Performance and Memory Efficiency

## Current reconciliation and ownership — 2026-08-24

| Slice | Current state | Evidence owner | Next gate |
|---|---|---|---|
| Pass truth and quarantine | Implemented, source-reviewed | MIR optimization layer | Execute focused pass/status/verifier specs |
| Shared local MIR facts | CFG/dominance/def-use/bounded liveness implemented | PerfFacts owner | Execute fact projection and malformed-CFG specs |
| Collection/vector safety | Unsafe hoist inert; vector analysis-only and unit-step bounded | MIR optimization layer | Keep disabled until legality/profitability proof |
| Escape authority | Unknown/return/field/size paths hardened | GC analysis owner | Execute escape regressions before allocation placement |
| Lint/tool hot paths | Shared views/indexes/policy/assembly tranches integrated | lint/tool owners | Same-fixture timing and peak-RSS comparison |
| Typed collection analysis | Initial request-local collector and fail-closed COLL002 candidate projection implemented | semantics performance owner | Generate verified stdlib registry, wire driver adapter, execute focused spec |
| Interprocedural/profile tiers | Not implemented | performance summary/profile owners | `.sperf`/`.sprof-v2` designs plus bounded evidence |
| Runtime acceptance | Blocked: admitted Stage-4 binary absent | bootstrap/release owner | Restore binary, then run each final gate once |

Parallel review lanes `pass_integrity_review`, `lint_perf_review`, and
`docs_plan_review` completed read-only current-HEAD audits. Merge and final
review remain owned by `/root`; their findings are reflected above and in the
current-head research reconciliation.

### Typed HIR facts tranche — 2026-08-24

- Owned files: `35.semantics/perf_facts`, its focused unit spec, and status docs.
- Complexity: one indexed worklist pass over immediate HIR children; no per-rule
  recursive traversal or front removal.
- Memory: request-local event/work arrays only; no global retained HIR or cache.
- Safety: resolved symbol + authoritative receiver type + verified versioned
  metadata are mandatory; Unknown never becomes a lint candidate or transform.
- Claim boundary: the current registry is fixture-only. Receipts and signature
  fingerprints are not authoritative until a post-resolution stdlib builder
  derives them from the resolved owner/signature; no driver warning is wired.
- Remaining integration: generate the standard-library metadata registry and
  adapt typed findings into driver-owned diagnostics without a second parse.
- Blocking dependency: repair the built-in collection method identity/runtime
  contract in `doc/08_tracking/bug/typed_collection_perf_builtin_identity_2026-08-24.md`;
  fixture symbols must not be promoted into production metadata.
- Runtime status: source-reviewed only while the admitted Stage-4 binary is absent.

## Diagnostic JSON serialization follow-up

- Merge owner: compiler performance/memory lane.
- Review evidence: parallel warning-policy audit identified duplicated five-pass
  whole-message escaping in both active query serializers.
- Implementation: place the exact one-pass escaper in `query_rich_common` and
  delegate both lint and compiler-diagnostic paths to it.
- Compatibility: retain the five legacy escapes, Unicode, JSON envelopes,
  diagnostic order and severity behavior.
- Performance acceptance: unchanged messages allocate no replacement buffers;
  escaped messages use one scan plus one final join rather than five full-text
  replacements.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and ownership review only.

## Workspace diagnostic session follow-up

- Add `compiler/90.tools/workspace_diagnostics` config/request/result/session
  owners; keep the first implementation serial and Pure Simple.
- Replace per-file `_run_simple_check` and nested JSON query subprocesses with a
  fresh per-file compiler/lint request inside one session.
- Preserve discovery and diagnostic order, clean-file JSON omission, summaries,
  exit codes and failure isolation; reset every mutable compiler/lint owner.
- Require zero per-file subprocesses and standalone/session parity fixtures before
  enabling the LSP path.
- Instance-own parser/lexer/AST state and add contamination stress coverage before
  any bounded parallel execution.
- Measure the same 50/200-file fixtures: cold/warm p50/p95, process count and max
  RSS; targets are >=50%/75% wall reduction and <=10% peak-RSS increase.

## Variable-reassignment dictionary tranche

- Replace analyzer-local count/alias parallel arrays and borrowed/escaped arrays
  with scalar dictionaries; retain shared legacy count helpers used by SSA lowering.
- Preserve raw scan order, exact-destination counts, old-root borrow/escape capture,
  alias resets, the 64-hop guard, local ID 0 and reason precedence.
- Remove unused non-alias escape collectors so they cannot be mistaken for the
  active, broader escape model.
- Pin copied-alias borrow followed by alias overwrite in both mirrored specs.
- Pin 256 distinct locals, exact reassignment total, safe flags and exact JIT fact
  ordering; do not derive output ordering from dictionary iteration.
- Performance acceptance: expected `O(I*64 + L)` lookup work and `O(L)` retained
  scalar state, with no growing parallel-array map/set in the active analyzer.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel semantic review only.

## Bare-import rewriter assembly tranche

- Replace the changed-file prefix concatenation loop with `new_lines.join("\n")`.
- Preserve split-derived blank lines, trailing-newline shape, matched-line output,
  atomic persistence and `-1/0/1` status behavior.
- Remove the now-unused text import and pin the shared-join/absence-of-prefix-loop
  contract in the existing atomic-rewriter spec.
- Performance acceptance: changed-file reconstruction copies `O(S)` output bytes,
  not `O(S*L)` cumulative prefixes; retained line storage remains unchanged.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel review only.

## Shared short-grammar identifier rewrite tranche

- Add canonical contains/plain/interpolation helpers to the cycle-free EasyFix
  rules-helper owner and both stdlib facades.
- Replace four compiler/stdlib immutable character-concatenation loops with thin
  delegates; remove discarded-output contains probes.
- Preserve ASCII whole-token boundaries, context-blind plain matching, Unicode,
  legacy boolean interpolation state, doubled braces, malformed braces, sequential
  tuple rewriting and the `_` no-change probe.
- Pin boundaries, Unicode adjacency, empty parameter, escaped/triple braces and
  all four delegation paths in mirrored short-grammar specs.
- Performance acceptance: unchanged input allocates no output; changed input uses
  match-proportional fragments and one join, with no growing result concatenation.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel semantic review only.

## MCP diagnostic wrapper assembly tranche

- Move wrapper JSON construction into cycle-free `query_rich_common`.
- Cache count text, append envelope/diagnostic/comma fragments and join once.
- Delegate active `query_diagnostics` and legacy `query_check` entrypoints to the
  shared emitter; preserve their public command behavior.
- Pin exact empty and multiple/nested-diagnostic output plus order and both caller
  delegations in mirrored query diagnostic specs.
- Performance acceptance: no full `diags_array` or structured-content
  intermediate; `O(S + D)` work, `O(D)` fragments and one final output allocation.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and parallel review only.

## ANSI-free query diagnostic follow-up

- Merge owner: compiler performance/memory lane.
- Add an ESC-presence fast path to `_strip_ansi`; return the original compiler
  output when ANSI stripping cannot change it.
- Preserve exact legacy ANSI/malformed-sequence behavior on the slow path.
- Pin plain Unicode, multiple terminated sequences and unterminated sequences in
  mirrored query-diagnostic contracts.
- Record workspace process-per-file work as the remaining architecture follow-up;
  repeated normalization is completed by the shared clean-output tranche below.
- Verification status: intentionally not executed under the user's explicit
  no-verify instruction; static diff and ownership review only.

## Completed shared query diagnostic normalization tranche

- Materialize combined cleaned compiler output once in active single-file and
  workspace callers while retaining raw stdout/stderr for text rendering.
- Feed lint policy and JSON parsing from the same immutable clean text.
- Count workspace text diagnostics from the exact line-admission predicate,
  without constructing JSON merely to obtain array length.
- Preserve stdout-before-stderr order, the inserted separator, duplicates,
  compiler-before-lint ordering, malformed ANSI behavior, and exit status.
- Add mirrored clean-view, policy, parse/count order, and active-source contracts.
- Verification intentionally not run under the user's no-verify instruction.

## Completed MCP bounded-text tranche

- Replaced quadratic JSON prefix assembly with an unchanged fast path and three
  ordered linear replacements.
- Removed byte-length/codepoint-index NUL corruption without the unsafe text
  iterator in both app and standard-library MCP serializers.
- Replaced first-lines prefix concatenation with append fragments plus one join
  while retaining truncation and trailing-empty behavior.
- Added paired behavioral specs/manual for Unicode, escaping, controls, limits,
  truncation, and newline edges.
- Recorded the duplicate-scan/child-startup target and freshness/parity/perf
  gates. Verification intentionally not run under the user's instruction.

## Completed MEXH004 cause-arbitration tranche

- Unified query and semantic unreachable-arm precedence.
- Replaced independent emission branches with one mutually exclusive decision,
  avoiding duplicate records and redundant suffix membership scans.
- Preserved diagnostic code, severity, query span, source order, coverage, and
  `MEXH006` collection.
- Added paired behavioral specs and a manual covering duplicate wildcard,
  after-wildcard, and pre-wildcard duplicate-pattern cases.
- Updated research, architecture, and detailed performance design. Manual
  verification intentionally not run under the user's instruction.

## Completed feature-document block-assembly tranche

- Replaced two growing-prefix text concatenations per documentation line with
  raw line fragments and one post-delimiter join.
- Reduced Pure Simple/C-native block construction from quadratic copied payload
  to linear join work plus an O(m) reference array.
- Preserved empty blocks, whitespace, metadata/title extraction, nested
  association, delimiter movement, and unterminated EOF behavior.
- Added real parser fixtures, focused behavioral/source contracts, and a manual.
- Scoped exact join evidence to Pure Simple/C-native paths; the Rust seed's
  multiple join entrypoints remain unclaimed without route-specific execution.
  Verification intentionally not run under the user's instruction.

## Completed manifest Remove quarantine tranche

- Audited schema loading, direct block/function/module adapters, and backend
  routing; confirmed arbitrary instruction deletion lacked def-use, effect,
  trap, dominance, and ownership proofs.
- Preserved v1 manifest and public API compatibility while making every
  execution surface an exact identity.
- Added early returns before O(I*R) matching, formatted operand keys, wildcard
  binding arrays, and unconditional MIR reconstruction.
- Changed backend-policy witnesses to retain a deliberately live copy while
  preserving bundled manifest/rule identifiers and v1 metadata compatibility.
- Updated research, architecture, runtime design, executable-spec prose, and
  generated manual expectations. Verification intentionally not run under the
  user's no-verify instruction.

## Completed lint-cache reverse-index tranche

- Canonicalize dependency membership for indexing without changing the public
  entry dependency list or `Dict<text, [text]>` representation.
- Apply old/new dependency deltas on store; leave unchanged buckets untouched.
- Remove every reverse link when an entry is overwritten or invalidated and
  delete empty buckets.
- Detach symbol buckets before invalidation traversal and deduplicate legacy
  repeated keys in the snapshot.
- Bound retained reverse-index slots by live unique edges rather than refresh
  history; preserve bucket encounter order and existing file invalidation
  cascade behavior.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed bulk-copy quarantine tranche

- Reopen the SG-1.3 bug because H1/H2 did not discharge the documented M1
  overlap/alias precondition.
- Make the direct elision adapter and module compatibility hook exact identities.
- Prevent `SIMPLE_MIR_BULK_OPS=1` from activating the rewrite.
- Preserve the dormant structural analysis API and backend intrinsic lowering;
  neither is transformation authority.
- Update canonical and rejected MIR witnesses to require unchanged element ops.
- Record reactivation gates: region/span non-overlap, dominance, H1/H2, trap and
  effect equivalence, activation witnesses, and semantic differential coverage.
- Remove the enabled-path Theta(I*L + I^2) analysis/rebuild cost by returning
  before function-key snapshots, local scans, whole-function rescans, or copies.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed WM module-path snapshot tranche

- Snapshot normalized module-path segments once after existing exemption exits.
- Reuse cached root and second segment across host-root, mutable-tier, and
  rendering-sublane policy scans.
- Preserve missing/empty segment behavior, sequential `std.`/`lib.`
  normalization, prefix boundaries, diagnostics, severity, and ordering.
- Reduce the `common.*` hot case from 26 split arrays plus 26 copies of every
  segment to one split array and one copy of every segment.
- Retain small ordered policy arrays instead of adding per-request hash maps.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed assertion-head boundary tranche

- Scan the exact ASCII assertion identifier alphabet on original statement
  bytes and materialize the head once.
- Strip leading underscores with one boundary scan and at most one slice.
- Preserve assertion families, required-space behavior, operand trimming,
  assignment exclusion, equality acceptance, and SPIPE005 diagnostic behavior.
- Reduce H-byte head/underscore processing from O(H^2) copied bytes and O(H)
  temporary slices to O(H) work with constant slice count.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed duplicate structural-key assembly tranche

- Preserve the exact identifier, number-with-dot, and unchanged-byte grammar of
  the cosine candidate prefilter.
- Assemble raw windows from ordered trimmed-line/newline fragments with one
  join, preserving empty lines and placing no separator after the final line
  fragment.
- Replace per-marker/per-byte immutable concatenation with ordered marker and
  maximal unchanged-span fragments plus one join.
- Reduce raw assembly from O(W*K) copied bytes to O(K+W), and normalized
  assembly from O(K^2) copied bytes to O(K), with O(W+F) fragment references.
- Keep authoritative tokenization, cosine vectors, candidate counts, file
  ordering, and public duplicate diagnostics unchanged.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed MIR local metadata-update tranche

- Share one guarded dense-index/unique-sparse fallback position resolver across
  local type reads, naming, and retyping.
- Replace full local-array reconstruction with one record replacement at the
  resolved position.
- Preserve missing-ID no-op behavior, field values not being changed, local
  order, unique sparse/reordered first-match behavior, and invalid duplicate-ID
  contract.
- Reduce canonical uniquely owned updates from O(L) forced copies to O(1) work
  and auxiliary storage; leave COW to copy only genuinely shared arrays.
- Remove setter-specific builder round-trip aliases from parameter, Vulkan,
  match, if, and conditional-chain lowering.
- Record the five merge sites whose earlier live branch-builder aliases can
  still trigger O(L) COW privatization; do not claim them as fully resolved.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed MIR-builder local-type index tranche

- Formalize the canonical append-only `LocalId == locals position` builder
  invariant in one bounds-checked lookup method.
- Retain a first-match scan fallback for unique-ID sparse or reordered direct
  fixtures; duplicate LocalIds remain invalid builder state.
- Route shared type lookup and explicit array/dict/string/float/bool/tuple/base
  predicates through the canonical method.
- Reduce Q canonical type queries over L locals from O(Q*L) comparisons to
  O(Q), without a side dictionary, cache lifetime, or MIR/API change.
- Leave local retype/name mutation unchanged for a separately reviewed tranche.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed no-allocation closure-index tranche

- Replace processed/queued array membership scans with one insertion-time
  discovered-path dictionary.
- Preserve initial directory order, first-import FIFO order, diagnostic order,
  one read per path, and existing public output.
- Reduce path-comparison work from O(V^2+E*V) to expected O(V+E), retaining
  O(V) queue/index storage and no persistent invalidation surface.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed canonical MIR DAG-validation tranche

- Build the unique block-id index once, retaining duplicate-ID diagnostic
  precedence ahead of terminator and target validation.
- Resolve and store ordered successor indices once while computing indegrees.
- Replace repeated full-block progress scans with an append-only Kahn queue and
  monotonic cursor.
- Deduplicate switch successors with a local indexed set while preserving
  default-first encounter order.
- Reduce adversarial validation from O(B^2+B*E+sum(k^2)) to expected O(B+T),
  where T counts raw successor entries; retain O(B+E) live graph storage plus
  O(max(k)) transient switch membership and no hash or API change.
- Manual verification intentionally omitted under the user's explicit
  no-verification instruction.

## Completed MIR verification atom-set tranche

- Replace growing state-atom, projected-effect, and written-region arrays'
  linear membership scans with operation-local dictionaries while retaining
  arrays for canonical sorting or first-occurrence output.
- Reduce deduplication from O(E*U), worst O(E^2), to expected O(E), followed by
  the unchanged O(U log U) sort and O(U) temporary membership storage.
- Preserve exact region/type atom identity, read exclusion, unique sorted
  output, frame canonical text, and hash semantics.
- Add an interleaved read and repeated-write contract proving duplicate
  collapse and canonical order.
- Verification intentionally not run under the user's no-verify instruction.

## Completed MIR verification manifest-index tranche

- Replace the per-effect scan of all prior effects with a manifest-local exact
  region-to-type dictionary while retaining every admitted effect in order.
- Reduce type-consistency validation from O(E^2) comparisons to expected O(E)
  lookups with O(R) request-local index storage.
- Preserve the first-conflict failure point and exact
  `FV2-E-REGION-TYPE-MISMATCH` diagnostic.
- Format source provenance only for `LoadGlobal` and `StoreGlobal`, reducing
  worst-case transient span text construction from O(I) validly-spanned
  instructions to O(G) validly-spanned global accesses without changing
  global span validation.
- Strengthen repeated-effect multiplicity and exact mismatch contracts;
  verification intentionally not run under the user's no-verify instruction.

## Completed TRK001 linear CSV-decoder tranche

- Replace character-by-character immutable field concatenation with one byte
  scan, maximal unchanged spans, boundary fragments, and one join per field.
- Reduce worst-case decoded-field copying from O(m^2) to O(m), eliminating one
  substring allocation per ordinary input byte.
- Preserve empty fields, quoted commas, mid-field quotes, conditional doubled
  quotes, unmatched quotes, edge trimming, UTF-8 bytes, row order, and line
  numbers.
- Add an exact `LintLevel.Deny`/message contract whose quoted identifier proves
  comma and doubled-quote decoding while quoted title/description exercise
  column alignment.
- Verification intentionally not run under the user's no-verify instruction.

## Completed API-surface snapshot assembly tranche

- Replace repeated edge slicing and character concatenation with one-pass ASCII
  trim/comma span scans.
- Mutate file, directory, and request entry accumulators through their unique
  local owners instead of rebinding returned `push` values.
- Remove the roots-sized count-only array while preserving `module_count ==
  roots.len()` for duplicate and empty roots.
- Replace cumulative SDN prefix concatenation with ordered fragments and one
  join, reducing worst-case assembly copies from O(P^2) to O(P).
- Preserve sorted file-read order, final module/symbol order, duplicate exports,
  exact grouping, and trailing newlines; correct the stale deduplication claim.
- Add ordered export parsing plus exact empty/multi-module serialization
  contracts; verification intentionally not run under the user's no-verify
  instruction.

## Completed adaptive MIR local-type index tranche

- Keep the first local-backed global access on the historical direct scan; on
  the second, build one first-declaration-wins LocalId-to-position dictionary.
- Cache serialized identities only for referenced locals and keep constant
  operands on their direct embedded-type path.
- Reduce repeated local lookup from O(G*L) to expected O(L+G) without adding
  index work to G=0/G=1 functions or adding a second eager serialization of
  unused recursive types.
- Preserve duplicate LocalId first-match behavior, missing load/store
  diagnostics, effect order/multiplicity, and canonical hashes.
- Reuse the repeated-access contract and add duplicate-ID, constant-store,
  exact indexed-missing, and adaptive source-topology contracts; verification
  intentionally not run under the user's no-verify instruction.

## Implemented generated HIR child-frame tranche

- Generator owner: add `HirChildFrame`, its context-neutral sink, reverse
  expansion, and allocating compatibility adapters.
- Collector owner: migrate `PerfFacts` traversal while preserving preorder,
  node counts, fact order, and loop-depth scheduling.
- Gate owner: extend generated visitor freshness to `hir_children.spl` and add
  wrapper/list/pair/order coverage.
- Merge owner: current compiler-performance lane.
- Final reviewer: normal-capability compiler reviewer after generated output
  regeneration; no sidecar result alone may approve ordering or COW semantics.
- Current status: generator, generated output, collector migration, and focused
  preorder fixture implemented. Manual verification remains excluded by the
  user's no-verify instruction and no self-hosted binary is deployed here.
- Freshness prerequisite completed: both visitor gates now isolate every
  generator output in temporary roots, and the combined gate includes a
  hand-edit-sensitive `hir_children.spl` comparison.

## Completed canonical lint-line migrations

- TYPE001/TYPE002, LEADOP001, const-reference-default, bare-primitive, and
  silent-default consume the one request-owned line snapshot.
- Source-taking APIs remain compatibility adapters for standalone callers.
- Exact finding parity fixtures pin code, operation, line, and message fields.
- Silent-default reuses the same lines for first-30 marker scope and finding
  detection, eliminating its second internal split.
- Next candidate: raw-RT requires a separate lexical/import evidence snapshot
  because it also owns
  byte-offset fixes and cannot be migrated mechanically.

## Completed VHDL deterministic-sort tranche

- Replaced quadratic catalog text and SymbolId selection scans with stable
  bottom-up merge ordering.
- Cached module-name and per-module category key snapshots across consumers.
- Added mirrored structural contracts for merge invariants, preserved raw
  comparators, overflow guard, removal of selection scans, and cache ownership.
- Parallel review covered complexity, array/COW ownership, stable tie behavior,
  odd runs, and current reverse-insertion behavioral coverage.
- Verification and optimizer execution intentionally not run under the user's
  no-verify instruction; no timing/RSS claim is made.

## Completed storage-layout overlap foundation tranche

- Replaced the global typed-fact pair scan with compact deterministic
  region-grouped interval ordering and distinct-field endpoint leaders.
- Preserved half-open, same-field, cross-region, identity-order, incomplete,
  and malformed externally constructed range behavior.
- Added direct-summary behavioral fixtures and mirrored structural contracts.
- Parallel lanes reviewed exact semantics, allocation/locality, sorting
  complexity, malformed ranges, and coverage gaps.
- Production reference inventory found no current pipeline caller, so this is
  activation-path hardening rather than a measured compiler speedup.
- Verification/optimizer/timing/RSS execution remains intentionally omitted
  under the user's no-verify instruction.

## Completed lint manifest-discovery tranche

- Confirmed prior work already provides one prepared config resolution and one
  parsed-append reuse per file; did not duplicate that solution.
- Disabled unused cwd manifest discovery/parsing only for target-scoped CLI
  linter construction while preserving direct-library defaults.
- Preserved the existing ancestor-cache and ten-level search semantics after
  review rejected distance-free path compression as horizon-unsafe.
- Added source contracts for constructor ownership and prepared resolution.
- Parallel lanes reviewed precedence, error ordering, profile/file overrides,
  cache freshness, filesystem probes, dictionary copies, and current coverage.
- Next allocation boundary: immutable command-effective manifest/CLI bases plus
  sparse file-attribute overlays to remove two override-dictionary copies/file.
- Verification, optimizer, timing, allocation, and RSS execution intentionally
  remain omitted under the user's no-verify instruction.

## Completed raw-SFFI source-view tranche

- Built one reference-backed docstring-filtered `CodeLine` snapshot for
  SFFI009 and SFFI010, replacing two independent snapshots.
- Preserved both public string APIs, path exclusions, lexical heuristics, line
  numbers, and call-before-declaration diagnostic ordering.
- Removed a redundant extern-name trim and duplicate body-indent scan.
- Added shared-snapshot behavior, category-order, exclusion, and source-owner
  contracts to the existing real raw-SFFI spec.
- Parallel lanes reviewed exact docstring quirks, boundary semantics, ordering,
  allocation multiplicity, matching complexity, and coverage gaps.
- Follow-up: replace `body lines * extern names * textual probes` with one
  lexical call-name scan and indexed extern membership.
- Verification, optimizer, timing, allocation, and RSS execution intentionally
  remain omitted under the user's no-verify instruction.

## Completed VHDL metadata-index tranche

- Built collision-framed exact and eligible-alias row-index maps once.
- Hoisted target-module alias normalization outside its function loop.
- Preserved direct+alias, duplicate exact/alias, invalid-row, generic-entry, and
  unmatched-row behavior.
- Added a real duplicate-exact ambiguity specimen plus mirrored source contracts.
- Static model: `Theta(F*N)` matching and alias substring churn become expected
  `O(F+N)` work with `O(N)` index keys/row ordinals.
- Verification intentionally not run under the user's no-verify instruction.

## Completed VHDL target-index tranche

- Indexed exact raw qualified/bare names for all and hardware-only functions.
- Preserved ambiguity counts, qualified errors, bare nil, and rewrite behavior.
- Removed per-edge key materialization, selection sort, full scan, and repeated
  qualified-identity construction.
- Reused behavioral coverage for unique/qualified/ambiguous calls and port maps;
  added mirrored structural complexity/diagnostic contracts.
- Static model: `O(E*F^2)` and `E*F` identity churn become expected `O(F+E)`
  with `O(F)` operation-local index state.
- Verification intentionally not run under the user's no-verify instruction.

## Completed VHDL trace-loop tranche

- Hoisted driver and catalog trace decisions after initial validation.
- Removed environment/text dispatch from metadata, rebase, and candidate loops.
- Preserved focused `core32_` stderr receipts and all generated data behavior.
- Replaced the empty catalog `keys().len()` materialization with `Dict.len()`.
- Added mirrored contracts for placement, guards, messages, and direct length.
- Static model: `N + 2F + M + 3` trace lookups become two per compile.
- Verification intentionally not run under the user's no-verify instruction.

## Completed LLVM adapter policy-hoisting tranche

- Snapshot compiler trace and bare-metal target mode once per direct compile.
- Feed one target decision to configuration and translator construction.
- Preserve the public IR translation API through a private policy-taking helper.
- Replace trace-only `functions.keys().len()` with direct dictionary length.
- Update bare-metal contracts and add mirrored trace/target contracts.
- Static model: trace env reads 8-to-1 or 2-to-1; target env+parse 2-to-1.
- Verification intentionally not run under the user's no-verify instruction.

## Completed MIR trace-scope tranche

- Added a nesting-safe dependency-leaf trace snapshot in `mir_data`.
- Balanced bootstrap and normal `lower_module` exits.
- Preserved separate general-lowering and MIRB-only semantics.
- Removed per-call MIRB environment lookup from `emit_call_value` and builder
  begin/end receipts.
- Generation-refreshed three former process-lifetime trace caches.
- Added mirrored contracts for aliases, exits, builder gates, and refresh.
- Static model: repeated three/four-flag conversions become four reads per outer
  module lowering; storage remains four i64 words.
- Verification intentionally not run under the user's no-verify instruction.

## Completed shared parser-profile gate tranche

- Reset the existing parser profiling tri-state once per parse boundary.
- Exported its suppression-aware decision to split declaration parsing.
- Removed per-method environment reads without changing enabled clocks, labels,
  or output intervals.
- Added mirrored source contracts for the shared owner and lazy zero sentinel.
- Static model: `M` environment/key/value conversions become one per parse;
  cache storage is unchanged and disabled clock/output work remains zero.
- Verification intentionally not run under the user's no-verify instruction.

## Completed FlatAstBridge trace-dispatch tranche

- Scoped the existing compiler-trace snapshot across fresh and restored flat
  AST module assembly.
- Migrated both split bridge modules to the cycle-free read-only accessor.
- Preserved dynamic `SIMPLE_BOOTSTRAP` behavior and both early/normal returns.
- Added mirrored structural contracts against direct trace env reads.
- Static operation model: up to 14 trace env/text lookups per bridge transaction
  become one; no new cache storage beyond the existing two-i64 scope state.
- Verification intentionally not run under the user's no-verify instruction.

## Completed frontend trace hot-path tranche

- Added one cycle-free parse-scope snapshot of `SIMPLE_COMPILER_TRACE`.
- Preserved dynamic behavior outside parsing, nested LIFO restoration, silent
  structured output, and resampling at the next top-level parse.
- Routed expression, statement, primary, module-body, and parser-type probes
  through the shared decision.
- Added mirrored same-process next-parse refresh contracts.
- Static operation model: about `15E + P + S` environment reads become one per
  top-level parse; constant two-i64 state; no AST/layout/API change.
- Cache-restore frontend conversion paths and remaining independent trace flags
  remain separate follow-up inventory; no broader cache claim is made.
- Verification intentionally not run under the user's no-verify instruction.

## Completed nested lint collection state tranche

- Harden `_collect_lint_diagnostics_json` as the lint-owned structured boundary.
- Snapshot/restore collection mode, outer records, severity map/count, and the
  private tier flag; return inner records as a separate ordered array.
- Preserve the legacy per-rule scalar and treat emitted array length as the
  authoritative serialized count.
- Reuse the pipeline's canonical source lines for file-attribute policy parsing,
  removing one full-source split and transient line array per linted file.
- Add mirrored source contracts and a top-level executable nested-state oracle.
- Parser trace stdout and parser/AST ownership remain separate blockers to
  workspace subprocess removal.
- Verification intentionally not run under the user's no-verify instruction.

## Completed silent frontend trace-scope tranche

- Add one cycle-free nested frontend trace-suppression owner.
- Enter before silent parser initialization and across structured lint parsing and
  AST walks; restore caller state on normal return.
- Gate optional reset/warning/profile/debug, parser-type, statement/expr tag/OOB,
  and parser-flow output while preserving cached-off hot paths.
- Collapse six expression-call trace environment probes to one decision per call
  allocation.
- Add mirrored subprocess contracts with ordinary traced positive controls.
- Keep workspace child isolation until cleanup-safe unwinding, structured safety
  failures, and parser/AST request ownership are complete.
- Verification intentionally not run under the user's no-verify instruction.

## Completed workspace diagnostic JSON scanner tranche

- Replace two per-byte-substring scans and the full interior copy with one
  byte-indexed scan over the original wrapper.
- Track string escapes, nested arrays and nested objects without changing the
  first exact compact-key or malformed-input contract.
- Append exact object slices locally, preserving order and duplicates without
  result-array reassignment.
- Add mirrored nested/string/escape/Unicode, empty, unterminated, whitespace-key,
  duplicate-order, and source-shape contracts.
- Verification intentionally not run under the user's no-verify instruction.

## Authority

Merge owner and final highest-capability reviewer: `/root`. Generated-manual review owner: `/root`. Sidecars may implement bounded disjoint lanes but cannot change frozen interfaces, accept exclusions, or mark done.

## Dependency graph

```text
W0 baseline/ownership
 -> W1 vector containment + pass contracts
    -> W2 frontend/diagnostics || W3 MIR facts
       -> W4 typed first-release rules
          -> W5 CollectionPlan/COW || W6 pass rehabilitation
             -> W7 CostSummary/.sperf
                -> W8 .sprof-v2/curves/profile ranking
                   -> W9 tool hot paths
                      -> W10 docs/refactor/verify
```

## Frozen shared names

`PassStatus`, `PassExpectation`, `BackendDelegation`, `PassRunRecord`, `EffectivePipeline`, `PerfRuleId`, `PerfDiagnostic`, `OperationSummary`, `CostExpr`, `AnalysisIncomplete`, `PerfFacts`, `LoopFact`, `MemoryRegion`, `PerfSummary`, `CollectionPlan`, `CowUniqueness`.

Frozen manual steps/helpers are those in the system-test plan and `.spipe/.../state.md`. Unimplemented helpers fail explicitly.

## Waves and ownership

| Wave | Owner lanes | Gate |
|---|---|---|
| W0 | merge owner; read-only inventory sidecars | admitted binary, dirty-file ownership, one baseline/provenance ledger |
| W1 | vector containment owner; pass-contract owner; tests-only owner | unsafe rewrite excluded; effective pipeline truthful; sentinel/verifier works |
| W2 | frontend-session owner; diagnostic-contract owner; tests-only owner | one revision owner, exact spans, legacy COLL compatibility |
| W3 | disjoint CFG/dominance, loop/range, def-use/liveness, region/memory, escape/COW lanes; one facade/invalidation owner | one CFG build/revision; unknown fails closed |
| W4 | disjoint copy/COW, collection, materialization/capacity, layout/stack, invariant/allocation rule lanes; one registry owner | first-release positive/suppression/unknown matrix |
| W5 | operation/cost, plan extraction, lowering, COW evidence lanes | only pure proven plans transform; true preheaders and zero-trip safety |
| W6 | one mini-lane per pass in selected order | full activation/differential/idempotence/adversarial/perf gate per pass |
| W7 | summary/cache, remaining rule families, `.sperf`, CI tests | deterministic bounded SCC and confident-only regression policy |
| W8 | profile codec, instrumentation, curves, ranking | v1 compatibility; disabled no allocation/I/O; profiles never legality |
| W9 | lint/LSP/MCP/cache/tool hot-path owners | warm no scan/subprocess; startup/request/RSS evidence |
| W10 | docs/manual/refactor owner then independent verifier | all REQ/NFR evidence current; STATUS PASS required for release handoff |

Shared registries/exports are edited by their single owner only. Sidecars submit integration deltas rather than editing shared files concurrently. No lane introduces `40.collection_plan` or a `65` layer.

## Baseline and verification commands

Use the exact admitted native pure-Simple binary and record its hash/provenance. Baseline focused compiler/lint/optimizer/COW/tool performance before source edits. For every touched `.spl` file, run `bin/simple run src/app/optimize/main.spl <file> --full --level=O3` once after stabilization. Then run focused correctness and the identical performance command once.

Final scope includes `check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, MCP stdio integration, owned-file lint/duplicate checks, direct env/process guards, optimizer integrity, requirement traceability, manual quality, and `find doc/06_spec -name '*_spec.spl' | wc -l` = 0.

## Risk gates

- No bulk pass activation.
- Unknown alias/effect/escape/range/cost rejects transformation.
- No raw runtime/env/process shortcut or Rust/C performance rewrite.
- No machine fix beyond ownership/lifetime/effect proof.
- No performance claim without same-binary provenance and repeated measurement.
- No profile-based semantic authorization.
- No implementation/done mark with fail-fast scaffold or missing manual.
- Maximum three fix/verify cycles per slice; stop and record remaining blocker.
## Active hardening tranche: SSA dominance receipts

- Merge owner: `/root`.
- Parallel review input: `ssa_verifier_design`, `verifier_integration_review`, and
  `architecture_perf_facts` lanes.
- Source owners: `mir_opt/perf_facts.spl` for bounded shared facts and
  `mir_opt/mod.spl` for optimizer-boundary policy.
- Acceptance: reject undefined, multiply-defined, use-before-def, non-dominating, and
  unavailable-dominance flows with stable codes; model call results on the normal edge.
- Performance gate: no verification work in normal builds, no dense liveness matrices in
  the verifier projection, and no definitions-by-uses Cartesian scans.
- Remaining follow-up: opcode typing, ownership, loop-boundary proof, exact module-pass
  outcomes, and admitted runtime differential evidence.

## Active hardening tranche: partial opcode typing

- Reuse the structural instruction traversal and one local-type index; do not add a
  second MIR walk or serialize type keys.
- Admit only exact local contracts for `Const`, `Copy`/`Move`, and `Cast`/`Bitcast`.
- Emit stable `MIRV025`-`MIRV027` codes and checked/unproved coverage counters at function
  and module level.
- Treat every other opcode as explicitly unproved until its full operand/result contract
  is designed and tested.
- Next type lanes: arithmetic/operator families, memory/pointer operations, aggregates,
  calls/signatures, SIMD/GPU, and terminators.

## Active tool tranche: allocation-free lint configuration membership

- Preserve the canonical `collection_performance` code mapping and evidence-tier policy.
- Replace per-entry `all_lint_names().contains` array construction/scanning in SDN and
  file attributes with allocation-free exhaustive membership.
- Pin enumeration/membership parity and reject the former source shape.
- Leave one-time enumeration consumers intact; do not introduce a mutable global cache or
  per-`LintConfig` registry dictionary.

## Active tool tranche: cached effective lint defaults

- Store the selected default-level table in `LintConfig` and refresh only on profile
  change.
- Share immutable defaults into child configs while copying only authored overrides.
- Require `get_level` to perform no registry construction, profile projection, source
  read, or allocation.
- Preserve collection evidence-tier warning caps and all allow/warn/deny behavior.
- Follow-up: cache project SDN parsing by path/revision and combine duplicate policy
  lookups only after output parity is pinned.

## Active tool tranche: request-local project policy reuse

- Bind file-parsed configuration to its exact `simple.sdn` source path.
- Skip reread/reparse when the base config already came from the discovered path.
- Retain only the immediately linted path/config for parsed AST rule append.
- Fail back to ordinary resolution on path mismatch; do not add a global cache without
  explicit revision invalidation and bounds.
- Follow-up: bounded directory-to-manifest cache keyed by canonical directory plus
  manifest size/mtime or digest for long-lived LSP/MCP sessions.

## Active tool tranche: one-pass diagnostic policy

- Introduce one evidence-aware suppression/severity decision record.
- Migrate central text/EasyFix filtering and parsed AST diagnostic append first.
- Preserve unknown-code, allow, warn, deny, typed-proven, and advisory-cap semantics.
- Pin absence of paired keep/level calls in migrated owners.
- Retain compatibility wrappers until query/LSP and remaining external callers migrate.

## Active tool tranche: shared request-local source view

- Add an explicit combined-lint entrypoint that retains the first line split.
- Reuse that COW view for parsed source-location indexing.
- Release on normal completion, non-Simple input, parse failure, and revision mismatch.
- Ensure ordinary/long-lived lint calls retain neither lines nor last-file policy.
- Follow-up: replace fallback location indexing with typed AST/HIR spans per producer.

## Active tool tranche: migrate line-view consumers

- Pass canonical lines into file-attribute policy resolution.
- Add compatibility `content` wrappers and allocation-free `*_lines` consumers.
- Migrate parameter-tag, raw-runtime fix, diagram, LLVM guard, name, freestanding, and WM
  owners without changing their order or predicates.
- Pin the normal call graph to line variants.
- Follow-up: extend the shared view through EasyFix registry owners and traceability rules.

## Completed tool tranche: quality-check line view

- Pass canonical lines to feature tracking, SPipe quality, and raw typed-UI checks.
- Remove five rule-local source splits without changing rule order or locations.
- Pin the normal call graph and forbid regression to content-taking method signatures.
- Follow-up: extend the shared view through EasyFix registry owners.

## Completed tool tranche: single EasyFix ownership

- Confirm `primitive_api` and `simple_script_required` are full-registry members.
- Remove their duplicate direct invocations and imports from normal lint.
- Pin registry membership and absence of duplicate call sites with source contracts.
- Follow-up: construct one bounded line/context view inside the registry.

## Completed tool tranche: shared SPipe EasyFix facts

- Add a canonical-lines registry entrypoint while retaining standalone compatibility.
- Build one request-owned `LineContext` array only for admitted spec files.
- Share contexts across four SPipe rules and lines with missing-docstring analysis.
- Pin normal lint dispatch and shared fact consumers with source contracts.
- Follow-up: migrate code/module/annotation EasyFix families into the same bounded view.

## Completed tool tranche: shared general EasyFix facts

- Construct one general request-owned context array from canonical lint lines.
- Migrate resource, struct, annotation, export/import-boundary, and SPipe consumers.
- Pass canonical lines to non-exhaustive-match and bypass analysis.
- Reuse lines/contexts in duplicate-typed-argument analysis, including per-signature calls.
- Preserve standalone compatibility wrappers and registry result order.
- Follow-up: index duplicate-typed call sites once and migrate remaining split-based rules.

## Completed tool tranche: compiler-owned EasyFix line migration

- Add canonical-line variants for star, wide-public, bare-bool, primitive, and script rules.
- Reuse shared contexts for short-grammar analysis.
- Add line-based file-scope allow handling for primitive APIs.
- Preserve allocation-free compatibility path gates on excluded files.
- Pin registry dispatch to every new view variant.
- Follow-up: migrate stdlib contextual-keyword/deprecation/stub scanners.

## Completed tool tranche: canonical EasyFix context owner

- Add stdlib `EasyFixSourceView` and a from-lines context builder.
- Add view entrypoints for contextual-keyword, deprecated-if-let, and stub rules.
- Re-export canonical stdlib context facts from compiler helpers; delete the duplicate type.
- Use one registry view for every compiler and stdlib context consumer.
- Pin single-view dispatch and absence of the compiler duplicate with source contracts.
- Follow-up: index duplicate-typed calls and audit remaining whole-source algorithms.

## Completed tool tranche: indexed duplicate-typed calls

- Count unique `(name, arity)` rewrite targets once and reject ambiguity fail-closed.
- Scan identifier/call sites once instead of once per signature.
- Store flat indexed replacements and restore signature/source order deterministically.
- Remove obsolete per-signature scan and uniqueness helpers.
- Pin indexed dictionaries and absence of the quadratic helper with source contracts.
- Follow-up: replace lexical candidates with typed resolved-call facts when available.

## Completed tool tranche: allocation-free annotation and EasyFix IDs

- Replace per-annotation whitelist arrays with exact allocation-free match dispatch.
- Decode namespaced and direct EasyFix ID formats through one helper.
- Fix W0404/W0406 policy identity so line numbers cannot become lint codes.
- Preserve malformed IDs as unknown authored codes rather than dropping diagnostics.
- Add functional ID-shape and source-allocation regression contracts.
- Follow-up: unify unknown decorator/attribute classification with typed annotation facts.

## Completed tool tranche: EasyFix policy reachability

- Compare emitted EasyFix semantic codes with configurable lint names/default levels.
- Add exact mappings for all already-declared EasyFix policy names.
- Map W0406 to the visibility-boundary family.
- Pin default-deny promotion and explicit-allow suppression behavior.
- Keep mapping allocation-free and shared by text/JSON policy projection.
- Follow-up: register intentional policy names for remaining advisory-only EasyFix codes.

## Completed tool tranche: advisory EasyFix policy completeness

- Register contextual, deprecated, struct, grammar, raw-unit, and SIMD policy names.
- Add warning defaults and allocation-free known-name membership.
- Map four short-grammar wire codes to one stable policy family.
- Pin direct/family mappings and authored allow suppression behavior.
- Follow-up: generate code/name/default parity from one machine-readable descriptor.

## Completed tool tranche: honest unknown-annotation fallback

- Add one union-based source fallback with one diagnostic per unknown annotation.
- Replace dual decorator/attribute registry scans with the generic owner.
- Register `unknown_annotation` and alias legacy policy names bidirectionally.
- Preserve legacy standalone rule entrypoints for compatibility.
- Pin known decorator/attribute suppression and unknown single-result behavior.
- Follow-up: move category-specific classification to typed HIR.

## Completed compiler tranche: remove unsafe hoist bodies

- Confirm both collection-hoist entrypoints are fail-closed identities.
- Delete unreachable header-insertion implementations and private-only helpers.
- Retain independently useful scalar/invariance analysis predicates without transforms.
- Pin absence of dormant rewrite markers/header insertion with source contracts.
- Keep real preheader/effect/alias/speculatability requirements explicit.
- Follow-up: implement LICM only on shared canonical loop and memory facts.
## Completed compiler tranche: remove dormant trip-count recognizer

- Keep loop trip counts unknown until SCEV-lite supplies the complete proof contract.
- Delete the unreachable comparison-bound recognizer and its private-only helpers.
- Pin the absence of dormant recognizer markers and helper names with a source contract.
- Preserve natural-loop discovery and complete `(from,to)` exit-edge facts.
- Follow-up: implement bounded SCEV-lite as a shared immutable analysis with explicit invalidation.
## Completed compiler tranche: remove unsafe dormant TCO

- Preserve the `Skeleton` descriptor, factory, statistics, and identity compatibility entrypoints.
- Delete the unreachable sequential parameter-assignment rewrite and private candidate helpers.
- Pin absence of the unsafe rewrite surface with a source contract.
- Require parallel temporaries and full arity/type/ownership/effect/unwind/debug proofs before rehabilitation.
- Follow-up: implement the active transform only after shared call-edge and ownership facts exist.

## Planned tooling tranche: CLI-scoped lint session

- Construct the lint descriptor registry once per repository command.
- Cache manifest discovery and parsed policy per unique project configuration.
- Load critical-mode policy once per command.
- Read each source once and share it with optional SIMD analysis.
- Keep `run_lint_file` as a one-file compatibility wrapper.
- Pin diagnostic ordering/policy equivalence and measure batch wall time plus maximum RSS.
## Completed tooling tranche: command-scoped lint registry reuse

- Add `run_lint_file_with_linter` and retain the standalone compatibility wrapper.
- Construct one `Linter` outside the repository file loop.
- Reuse the most recent parsed project policy through a command-owned bounded cache.
- Clone cached policy before file/CLI overrides to prevent cross-file mutation.
- Pin registry construction and cache ownership with source contracts.
- Follow-up: cache manifest discovery and critical policy, then share one source read with SIMD/fix paths.
## Completed tooling tranche: one lint/SIMD source read

- Add a source-owned command entrypoint while retaining file-reading compatibility wrappers.
- Read each repository source once through the tagged lint reader.
- Share the exact payload with ordinary lint and optional SIMD analysis.
- Preserve valid-empty-file versus read-error behavior.
- Keep fix application on a fresh validated disk read before mutation.
- Follow-up: cache directory-to-manifest and critical-mode policy resolution.
## Completed tooling tranche: critical policy session snapshot

- Resolve `critical.dynamic_acquire` lazily on first linted file.
- Retain only the effective scalar mode in the command-owned `Linter`.
- Reuse disabled/allow state without rereading or reparsing configuration.
- Pin one-load session ownership with a source contract.
- Follow-up: add bounded directory-to-manifest discovery caching.
## Completed tooling tranche: bounded manifest discovery

- Cache source/common-ancestor directory outcomes, including manifest misses.
- Consult cached ancestors before filesystem probes.
- Cap retained directory entries at 4096 and fall back to correct uncached discovery.
- Mark caller-prepared paths so lint policy resolution does not repeat the walk.
- Continue cloning policy before file-local attributes.
- Follow-up: extend parsed-policy caching from the adjacent-project slot to bounded unique manifests.
## Completed tooling tranche: bounded parsed-policy cache

- Replace the adjacent-only project-policy slot with a path-indexed flat cache.
- Retain at most 256 unique parsed manifests per command.
- Clone cached base policy before CLI and file-local overrides.
- Avoid struct-valued dictionary retrieval by storing integer indexes.
- Preserve uncached parsing after saturation.
- Follow-up: reuse `LintConfig.new()` defaults for manifest-free files without mutable sharing.
## Completed tooling tranche: shared manifest-free defaults

- Build the default lint-level dictionary once per command-owned `Linter`.
- Give each manifest-free file an isolated child configuration.
- Share immutable effective defaults while keeping overrides mutable per file.
- Pin absence of per-file `LintConfig.new()` in the no-manifest branch.
- Follow-up: reduce CLI argument policy rescans to one parsed command policy.
## Completed compiler tranche: storage-layout advisory indexing

- Replace growing-array field-ID deduplication with dictionary membership and an explicit count.
- Remove the redundant field-ID array allocation.
- Replace handwritten selection sort with the standard deterministic sort.
- Preserve identity format, completeness decisions, and overlap semantics.
- Follow-up: design a region-grouped interval sweep for overlap proof before changing the remaining pair analysis.
## Completed compiler tranche: remove incomplete string-builder rewrite

- Preserve the `Skeleton` class, factory, statistics, and identity entrypoint.
- Remove private concat candidate/rewrite machinery and unused loop-detector/local-ID state.
- Pin absence of push-only lowering with a source contract.
- Require typed builder construction, initialization, final joins, dominated use replacement, and semantic differential tests before rehabilitation.
- Follow-up: prefer CollectionPlan producer-consumer lowering once ownership/effect/cardinality facts are complete.
## Completed compiler tranche: close strength-reduction bypass

- Preserve provider metadata, class/factory compatibility, statistics, and zero-change receipts.
- Make direct function and block entrypoints identities while status is disabled.
- Remove signed arithmetic, decomposition, and synthetic-local rewrite helpers.
- Replace legacy transformation fixtures with fail-closed/source contracts in both test layouts.
- Follow-up: rehabilitate individual rewrite families only with per-operation range/type/overflow proofs and differential tests.
## Completed compiler tranche: remove unsafe dormant GVN

- Preserve the `Skeleton` class, factory, dependencies, statistics, and identity wrapper.
- Remove direct block-order value-numbering and cross-block rewrite entrypoints.
- Delete text-signature tables and unscoped field-load reuse.
- Pin absence of the block-order implementation with a source contract.
- Follow-up: rehabilitate only on dominators, structural keys, and MemorySSA-lite versions.
## Completed compiler tranche: close BCE direct-call bypass

- Preserve proof record types, counters, dependencies, factory, and compatibility methods.
- Make function and block entrypoints identities while status is disabled.
- Remove global loop-proof seeding, textual check keys, and direct instruction deletion.
- Replace simulated-elimination fixtures in both test layouts with fail-closed contracts.
- Follow-up: rehabilitate only with dominance-scoped SSA/range/mutation facts and differential safety tests.
## Completed compiler tranche: close general loop-transform bypasses

- Preserve LICM/unroller/combined classes, counters, thresholds, factories, dependencies, and identity compatibility methods.
- Remove preheader synthesis, predecessor redirection, instruction movement/duplication, and direct combined chaining.
- Remove per-instance loop detectors from disabled transforms.
- Replace simulated transformation fixtures in both test layouts with quarantine contracts.
- Follow-up: rehabilitate only on canonical LoopForest, SSA, MemorySSA-lite, effect and profitability facts.
## Completed compiler tranche: quarantine generator state-machine rewrite

- Preserve exported yield point/analysis types, discovery, class/factory/statistics, and identity methods.
- Remove dispatcher/signature/local/state-block construction and private segment lowering.
- Replace per-yield whole-function definition rescans with one forward definition walk plus conservative local snapshots.
- Pin separation of analysis and transformation with a source contract.
- Follow-up: move admitted coroutine lowering to an ABI/runtime owner backed by shared CFG liveness and ownership facts.

## Completed compiler tranche: quarantine body outlining

- Preserve exported compatibility analysis classes, counters, factory, and identity function/module entrypoints.
- Remove dormant cold-region grouping, liveness, CFG extraction/remapping, and synthetic-function construction.
- Pin absence of direct rewrite machinery with a source contract.
- Count the deletion as compiler parse/compile, allocation, and code-footprint reduction; do not claim runtime speedup without measurement.
- Follow-up: rehabilitate only with canonical region facts, complete SSA/ownership/unwind/debug proofs, checked module construction, profitability, and differential tests.

## Completed compiler tranche: quarantine local CSE

- Preserve exported expression/table/class/factory/statistics compatibility with fail-closed lookup and transform surfaces.
- Remove direct MIR rewrite, mutable leader selection, incomplete invalidation, and per-expression table operations from the Skeleton path.
- Pin absence of rewrite construction with a source contract.
- Record removed text hashing, dictionary churn, array cloning, and dead compiler source as compile-time/memory improvements without claiming runtime benefit.
- Follow-up: activate Copy-only local propagation first; then shared-semantics constant folding; rehabilitate CSE only with structural keys, ownership, kills, effects/traps, and MemorySSA-lite; defer DCE until observability and sparse-liveness budgets are proved.

## Completed tooling tranche: command-scoped lint CLI policy

- Parse deny/warn, output, fix, WM-lane, and profile options once per repository command.
- Pass a constant-size `LintCliPolicy` into each source invocation rather than the positional target array.
- Preserve standalone args wrappers and manifest → CLI → file-header precedence.
- Pin absence of per-file argument membership/profile scans with a source contract.
- Reduce explicit N-file policy work from quadratic argument comparisons to one linear command parse plus O(1) per file; retain only constant-size policy state.
- Follow-up: replace source-sized retained line arrays only after an explicit borrowing/ownership design.

## Completed compiler tranche: quarantine copy propagation

- Preserve exported `CopyChain`/`CopyPropagation` shapes, zero counters, factory, and identity wrapper.
- Remove partial block/instruction/operand/terminator rewrites and fixed-depth copy-chain walking.
- Replace simulated copy-to-move fixtures and their manual with honest fail-closed contracts.
- Record eliminated MIR-array rebuilding, chain traversal, dead parsing/compilation, and source footprint as compiler performance/memory improvements.
- Follow-up: implement exhaustive block-local Copy-only propagation with near-linear roots, ownership exclusion for Move, exact receipts, verification, and semantic differential witnesses.

## Completed compiler tranche: isolate legacy optimizer function state

- Reset constant, type, definition, use-count, and expression maps at every function entry, including the `None_` early return.
- Preserve cumulative statistics and configured optimization level.
- Add mirrored regressions proving all retained entries are released and statistics remain cumulative.
- Count prevention of cross-function `LocalId` contamination as correctness and release of retained MIR/dictionary state as memory hardening.
- Follow-up: remove the semantic HIR constant-fold no-op traversal; keep semantic constant evaluation and canonical MIR folding distinct.

## Completed compiler tranche: remove discarded HIR constant folding

- Delete the semantic HIR pass that rebuilt bodies but never installed them.
- Remove driver invocation and semantics-barrel exports; route `resolved_module` directly into bootstrap validation storage.
- Preserve semantic `const_eval` and canonical typed-MIR constant folding as distinct owners.
- Add mirrored source contracts for driver, barrel, removed file, and retained const evaluation.
- Count eliminated evaluator construction, function/expression traversal, and temporary HIR arrays as active compiler CPU/memory improvement.
- Follow-up: quarantine or rehabilitate the canonical MIR constant-fold direct method with shared arithmetic/result-type semantics.

## Completed tooling tranche: compact lint parsed-handoff state

- Build fallback source-location dictionaries during the existing canonical text-line traversal.
- Retain only function, collection-fix, and star-export location maps across parsing; remove full split-line state.
- Materialize config/index and release handoff state before AST diagnostic loops.
- Preserve defensive fallback indexing and all early-return releases.
- Pin absence of `last_source_lines` and immediate release with source contracts.
- Follow-up: evaluate result-array in-place compaction only after value-semantics/alias tests prove it safe.

## Completed compiler tranche: quarantine MIR constant folding

- Preserve evaluator, simplifier, pass, factory, method, statistics, and wrapper compatibility as zero-change/`nil` surfaces.
- Remove untyped host arithmetic, algebraic rewrites, branch rewrites, and unconditional MIR-array reconstruction.
- Replace direct-transform fixtures/manual with effective-pipeline and fail-closed contracts.
- Record deleted source/IR, avoided direct-call allocations, and malformed-result prevention as compiler performance/memory/correctness hardening.
- Follow-up: design one shared typed evaluator with exact target semantics, structured rejections, changed flags, receipts, verification, and differential tests.

## Completed tooling tranche: compact lint results in place

- Replace the second filtered result array with stable request-owned read/write compaction.
- Preserve ordering and construct isolated records only for severity changes.
- Truncate the tail after the captured original range is fully scanned.
- Pin `write <= read` algorithm shape and absence of the second buffer with source contracts.
- Reduce peak diagnostic reference/capacity retention without relying on mutable aliases.
- Follow-up: migrate remaining safe split-based lint wrappers to the canonical line view; preserve intentionally transformed/masked views.

## Completed compiler tranche: quarantine dead-code elimination

- Make every DCE transform entrypoint identity while status is `Skeleton`.
- Remove dense liveness construction, block/local scans, keep bitmaps and MIR
  rebuilding from the callable Skeleton path.
- Preserve mandatory probe classification as analysis-only compatibility and
  fail side-effect/purity decisions closed.
- Replace positive deletion fixtures/manual claims with quarantine contracts.
- Follow-up: separate `perf_facts_build_without_liveness` for production
  consumers that do not need dense liveness; rehabilitate DCE only with sparse
  liveness and exhaustive opcode semantics.

## Completed compiler/tooling tranche: scoped facts and linear diagnostics

- Add a named no-liveness PerfFacts builder and retain the verifier API as a
  compatibility alias.
- Migrate loop detection, auto-vectorization analysis, storage-access analysis,
  and typed-storage-view production away from dense liveness.
- Pin empty matrices/zero worklist behavior and the four production call sites.
- Replace human and JSON diagnostic evidence append loops with one join while
  preserving exact output ordering.
- Follow-up: introduce integrity-checked `PerfFactRequest` projections, and
  migrate the accessor-field lint from repeated source splits and
  `O(methods^2 + lines*methods)` scans to canonical source views and indexes.

## Completed tooling tranche: index accessor field rewrites

- Add line-based accessor-class parsing while preserving the source wrapper.
- Route the active fix registry through canonical lines and contexts.
- Replace repeated suffix and line-by-dummy scans with per-class dictionaries
  plus actual call-name extraction.
- Reuse canonical byte offsets and remove the redundant starts array.
- Preserve exact getter/setter rewrite guards and fail closed on ambiguous names.
- Follow-up: route the legacy aggregate easy-fix registry through one shared view
  and profile remaining rules that still accept raw source.

## Completed warning-system tranche: bound candidate and delimiter scans

- Reject non-public/extern lines before `primitive_api` item-suppression scans.
- Preserve file/item allow semantics and advance offsets once per line.
- Replace suffix-based spec-docstring counting with one absolute forward cursor.
- Remove duplicate silent-default warning entrypoints and pin one owner.
- Follow-up: implement dependency-closed `PerfFactRequest` presets so CFG-only
  and def-use-only analyses stop building unrelated fact families.

## Completed compiler tranche: request exact PerfFacts capabilities

- Add dependency-closed requests and diagnostics for hidden expansion.
- Keep full, no-liveness and verifier builders as compatibility wrappers.
- Migrate loop detection to CFG plus dominators without instruction def-use.
- Migrate storage access to def-use only and block-keyed vector/storage rewrite
  consumers to CFG+def-use without RPO/dominators.
- Keep every unrequested fact family empty and incomplete.
- Follow-up: expose requested/effective capabilities in optimization telemetry
  and replace the hard-coded liveness cell cap with a named budget policy.

## Completed review hardening: PerfFacts capability integrity

- Add explicit dominance completeness and gate loop discovery on it.
- Add CFG+def-use preset without RPO/dominance/liveness.
- Require CFG integrity for vector dependency analysis and typed-storage rewrite.
- Reject duplicate block identities before block-keyed def-use interpretation.
- Retain def-use-only storage-access analysis because incomplete facts become
  conservative unknown access rather than transformation authority.

## Completed tooling tranche: linearize wide-public deduplication

- Replace growing export-name array membership scans with a dictionary set.
- Maintain an explicit unique-export count rather than relying on dictionary
  length behavior.
- Preserve facade, wildcard, re-export, whitespace, comment and duplicate rules.
- Remove the single-use linear `list_has` helper.
- Follow-up: inventory remaining canonical lint dedupe arrays and distinguish
  count-only membership from ordering-sensitive result storage.

## Completed tooling tranche: skip inactive diagnostic policy work

- Guard serialized diagnostic code extraction with an explicit override count.
- Maintain the dictionary/count pair only at lint-config load and clear boundaries.
- Preserve suppression, severity rewriting, collection, and direct-print behavior.
- Avoid native dictionary length as a hot-path correctness predicate.
- Follow-up: replace serialized JSON policy projection with typed diagnostics.

## Completed compiler tranche: linear predecessor adjacency

- Replace per-edge dictionary array copyback with indexed owned buckets.
- Publish one predecessor array per distinct successor after edge discovery.
- Preserve edge multiplicity, predecessor order, dangling-edge evidence, and
  malformed-CFG counters.
- Pin a high-fan-in/duplicate-edge example plus a source regression guard.
- Follow-up: gate dense liveness allocation before matrix construction on every
  incomplete-input path.

## Completed tooling tranche: linear short-lambda discovery

- Replace recursive next-backslash discovery and prefix rescans with one pass.
- Preserve comment cutoff, quote toggling, eligibility, replacement ordering,
  and consumed-range suppression.
- Pin quoted, live, and commented backslashes plus absence of recursive helpers.
- Compute the functional-update boundary once rather than rescanning it for each
  candidate; continue inventorying syntax-dependent candidate parsers before
  claiming an end-to-end linear short-grammar rule.
- Follow-up: share a lightweight lexical line-state service across source rules
  instead of retaining rule-local quote/comment models.

## Completed compiler tranche: fail-fast liveness allocation

- Reject incomplete CFG/def-use inputs before live-in/live-out allocation.
- Skip USE/DEF allocation when duplicate locals already make def-use incomplete.
- Release USE/DEF working matrices when later validation fails closed.
- Preserve complete liveness results, visit budgets, and oversized-input status.
- Pin duplicate-local, uncovered-instruction, and dangling-edge empty-storage
  contracts.

## Completed tooling tranche: unchanged diagnostic identity fast path

- Compute CLI effective severity once per diagnostic.
- Return the immutable result directly when severity is unchanged.
- Rebuild only actual Warn-to-Deny transitions.
- Preserve text/JSON bytes, ordering, counts, fixes, evidence, and uncertainty.
- Follow-up: move policy projection before serialized output ownership entirely
  when typed diagnostic transport replaces compatibility JSON.

## Completed compiler tranche: linear loop-latch aggregation

- Index first-seen natural-loop headers into owned latch buckets.
- Deduplicate source/header edges with per-header membership dictionaries.
- Preserve loop order, backedge order, duplicate-edge coalescing, bodies, and exits.
- Remove dictionary-held growing-array extraction and copyback.
- Pin ordered multiple latches with a duplicate-target terminator.

## Completed tooling tranche: bounded fix assembly

- Stable-merge every replacement batch by descending start.
- Preserve equal-start insertion order through left-first equality.
- Assemble valid non-overlapping edits from source chunks with one join.
- Retain incremental behavior for negative, reversed, or out-of-range spans.
- Pin multi-edit output, equal-start insertion order, and invalid-span skipping.
- Replace per-file dictionary array copyback with owned indexed buckets while
  preserving dictionary key iteration and per-file replacement order.
- Consolidate ordering and assembly in the stdlib EasyFix owner.
- Delegate compiler FixToolApplicator and route lint fix through shared primitives.
- Remove every private and equal-start quadratic sort/repeated-splice implementation.

## Completed lint tranche: indexed SPIPE005 helper reachability

- Return typed bare-call names instead of delimiter-backed strings.
- Build local reverse-call buckets once and propagate through a queue.
- Preserve duplicate textual-name union, forward references, cycle semantics,
  and method-call exclusion.
- Add mirrored behavioral contracts for cycles, methods, and duplicates.
- Verification intentionally not run under the user's no-verify instruction.

## Completed structural-union symbol/narrowing tranche

- Add module-lifetime forward/reverse structural-union SymbolId maps to
  `SymbolTable`, reset, and codec transport.
- Recompute the preferred lane ID from canonical identity so caller hints
  cannot perturb assignments; bound collision probing and fall back to a
  unique ordinary ID without aliasing.
- Route enum and variant synthesis plus HIR narrowing through the same owner.
- Resolve bare named pattern types to their registered SymbolId and canonical
  member key.
- Build one key-to-variant dictionary per rewritten match.
- Correct nested-union member keys to shared ordered equality semantics.
- Deferred: generic/qualified type-pattern grammar and deep structured-key
  interning/streaming; pre-sorted preregistration for encounter-independent
  assignment under genuine FNV collisions.
- Verification intentionally not run under the user's no-verify instruction.

## Completed name-lint indexing tranche

- Finalize each parsed class once instead of copy-modify-reassigning it for
  every method, and reuse each method-body scan endpoint.
- Build one first-definition class index and one ordered inheritance fact per
  class for both ACC001 and NAME001.
- Replace suffix dedup and suffix-by-method rescans with indexed flat groups,
  preserving exact legacy diagnostic grouping and order.
- Add mirrored contracts for group order, duplicate-class/transitive lookup,
  and nested textual-class behavior.
- Implemented: allocation-bounded three-row edit band with byte comparisons.
- Deferred: compact first-statement storage for NAME001/ACC001.
- Verification intentionally not run under the user's no-verify instruction.

## Completed query outline-index tranche

- Build return-type and parameter-name facts together from the already-split
  source lines.
- Replace parallel-array linear call-site lookups with dictionaries while
  preserving first-definition/first-nonempty-return behavior.
- Make the former duplicate inlay module a narrow compatibility re-export.
- Add direct duplicate-precedence and source-ownership contracts.
- Deferred: cache parsed parameter vectors if profiling shows per-call splitting
  is material.
- Verification intentionally not run under the user's no-verify instruction.

## Completed formatter fingerprint tranche

- Replace immutable accumulator concatenation in token and comment-gap
  fingerprints with ordered fragments and one join.
- Preserve exact lexical-equivalence framing and failure behavior.
- Add comment-byte/order and source-shape regression contracts.
- Deferred: evaluate streaming fingerprint comparison only with representative
  measurement and exact mismatch semantics.
- Verification intentionally not run under the user's no-verify instruction.

## Completed CLOS001 scope-index tranche

- Use a prefix-maximum indentation index for exact prior-boundary lookup.
- Share incrementally advanced declaration counts across sibling closures with
  the same textual boundary and indentation.
- Preserve duplicate warning multiplicity, body/order/span, boundary quirks,
  and assignment syntax.
- Remove stale extra emitter arguments from query-check lint calls.
- Add production-path duplicate/sibling ordering and source-shape contracts.
- Deferred: replace overlapping nested-body scans with an offline assignment
  interval join while preserving legacy double reporting.
- Verification intentionally not run under the user's no-verify instruction.

## Completed structural-union canonicalization tranche

- Make member keys exhaustive and consistent with `hir_types_equal`.
- Use numeric text atoms and length-framed lists so canonical keys and sanitized
  variant identifiers cannot alias through delimiter/punctuation ambiguity.
- Replace linear deduplication and insertion rebuilding with dictionary dedup
  plus stable bottom-up merge ordering.
- Return one `UnionNormalized` result and reuse it in synthesis, registration,
  and narrowing.
- Replace linear module registration membership with a dictionary.
- Add direct permutation, flatten/optional, omitted-field, wrapper, and source
  complexity contracts.
- Track synthetic SymbolId collisions and named-type narrowing separately.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic runtime tranche: fixed-pattern automaton

- Intern 116 fixed classifier literals into 1,160 sparse Aho-Corasick states.
- Scan each diagnostic byte string once into two local `u64` hit masks.
- Preserve all 80 ordered predicates, the negative `function` guard, explicit
  code precedence, shadowed rules, case sensitivity, and arbitrary dynamic
  codegen phrase behavior.
- Add mirrored every-literal, Unicode-neighbor, suffix-output, case, and
  no-match contracts.
- Retain one dynamic phrase search at its exact rule priority.
- Follow-up: add the deterministic Pure Simple generator and stale-data gate
  tracked in `doc/08_tracking/bug/query_error_matcher_generation_freshness_2026-08-22.md`.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic tooling tranche: deterministic matcher generation

- Added the canonical append-only 116-pattern Pure Simple manifest.
- Added a bounded deterministic trie/failure/CSR/output-mask model builder.
- Added one-join source rendering, non-mutating exact `check`, and changed-only
  atomic `generate` modes without process, shell, C, or Rust delegation.
- Added mirrored manifest alignment, cardinality, exact source freshness, and
  injected-bound failure contracts.
- Added an 80-row postfix predicate manifest and seven-row fallback manifest.
- Added fail-closed priority, postfix arity, pattern-ID, E-code, and sole dynamic
  phrase validation plus exact generated-block freshness ownership.
- Completed direct constant-mask rule emission across low/high `u64` boundaries,
  removing about 135 helper calls and variable shifts on late/no-match paths.
- Remaining follow-up: stale-file CLI red fixture and executed latency/RSS
  evidence when verification is permitted.
- Completed bounded leading `Edddd` validation: reject non-`E` without a slice,
  then validate one five-byte candidate to avoid repeated raw-string `strlen`.
- Verification intentionally not run under the user's no-verify instruction.

## Completed diagnostic tranche: shared query error-code ownership

- Move the duplicated ordered classifier into cycle-free `query_error_codes`.
- Parameterize the legacy `FFI error` / active `SFFI error` distinction.
- Preserve malformed explicit codes, case sensitivity, overlap order, and exact
  error-kind fallbacks with mirrored contracts.
- Replace 473 entry-local lines with one 242-line owner plus four wrapper lines
  (net 227-line reduction).
- Completed next: replace the remaining fixed probes with an immutable sparse
  multi-pattern matcher without constructing a registry per call.
- Verification intentionally not run under the user's no-verify instruction.

## Completed lint lexical-snapshot tranche

- Add one neutral `CodeLineSnapshot` owner in `lint_text` with the exact legacy
  triple-quote state machine and an explicit release boundary.
- Share one snapshot across module-init/COW checks and a second across
  unwrapped-resource/raw-SFFI checks, reducing four full lexical projections to
  two while avoiding whole-request retention.
- Preserve public source adapters, per-rule path exclusions, physical line
  numbers, complete finding order, raw text, and trimmed text.
- Add a real projection/lifetime fixture covering multiline and one-line
  docstrings; verification intentionally not run under the user's no-verify
  instruction.

## Completed dynamic-capability line reuse tranche

- Add canonical-line kernels for the DCA file-scope decision and acquisition
  scan; keep source APIs as compatibility adapters.
- Route the main lint driver through its existing line array, removing the two
  DCA-owned full-source splits in critical mode.
- Preserve allow-mode early return, configured severity, group matching,
  acquisition ordering, physical lines, and complete finding payloads.
- Add complete-field source/lines parity coverage; verification intentionally
  not run under the user's no-verify instruction.

## Completed RISC-V RTL line reuse tranche

- Add a `source + canonical lines` debuggability kernel and retain the source
  API as a compatibility adapter.
- Reuse the main lint driver's lines for source-map and output-port scans,
  removing two generated-VHDL splits without conflating the separately loaded
  products manifest.
- Preserve path gating, sidecar/manifest I/O order, warning order, severity,
  messages, hints, physical location, and file path.
- Add generated-bundle complete-field parity coverage; verification
  intentionally not run under the user's no-verify instruction.

## Completed critical-file line-count tranche

- Replace CFG002's per-file `split("\n").len()` with one-pass newline counting.
- Preserve exact split-count behavior for empty files, blank lines, and trailing
  newlines while reducing auxiliary storage from O(lines) to O(1).
- Keep configuration parsing unchanged because that path consumes actual line
  contents rather than only their count.
- Add direct boundary coverage; verification intentionally not run under the
  user's no-verify instruction.

## Completed tool line-count tranche

- Replace count-only split arrays in context metadata, LLM Caret message
  statistics, and SPipe documentation validation with direct newline scans.
- Preserve the two distinct empty-input contracts: zero for context/message
  statistics and one-per-block for SPipe split compatibility.
- Preserve trailing-newline final segments and reduce auxiliary storage from
  O(lines) to O(1) without changing outputs or public APIs.
- Add context and SPipe boundary coverage; verification intentionally not run
  under the user's no-verify instruction.

## Completed optimizer stable-name integrity tranche

- Require every registered descriptor's stable name to resolve to the same
  `PassKind`, in addition to existing alias/status/expectation checks.
- Fail closed with distinct unresolved-name and wrong-kind reasons.
- Replace quadratic array membership in registry and witness uniqueness checks
  with dictionary sets.
- Add positive, missing-name, and misbound-name contracts; verification
  intentionally not run under the user's no-verify instruction.

## Completed optimizer registry snapshot tranche

- Materialize the descriptor/provider registry once per combined integrity
  audit and reuse it across status, witness, alias, and fact phases.
- Add a private snapshot-taking witness kernel while retaining the public
  no-argument compatibility check.
- Preserve finding order and payload while removing two full registry/provider
  reconstructions from the combined path.
- Existing positive registry/witness integrity contracts cover behavior;
  verification intentionally not run under the user's no-verify instruction.

## Completed optimizer descriptor-reuse tranche

- Split backend policy evaluation into a resolved-descriptor kernel and the
  public name-resolving compatibility adapter.
- Reuse one descriptor per pass in budget-filtered pipelines and deterministic
  optimization reports instead of reconstructing provider metadata twice.
- Preserve unknown/missing-pass rejection, canonical stable names, status,
  backend delegation, cost budget, report schema, and ordering.
- Existing backend-decision and deterministic report contracts cover behavior;
  verification intentionally not run under the user's no-verify instruction.

## Completed optimizer report assembly tranche

- Replace cumulative top-level JSON concatenation with ordered pass-entry
  accumulation and one final join.
- Preserve schema bytes, ordinals, status/reason fields, backend outcomes,
  commas, empty-pipeline rendering, and deterministic ordering.
- Reduce top-level report assembly from cumulative-prefix copying to O(output)
  work and storage.
- Existing deterministic report contracts cover behavior; verification
  intentionally not run under the user's no-verify instruction.

## Completed SIMD recipe report tranche

- Replace growing-prefix recipe report concatenation with ordered fragments
  and one final join.
- Preserve header count, insertion order, entry summary fields, indentation,
  and one trailing newline per entry.
- Keep the current 16-entry bound while ensuring future bound growth does not
  make report assembly cumulatively copy prior output.
- Add a direct deterministic report contract; verification intentionally not
  run under the user's no-verify instruction.

## Completed PerfFacts fixed-allocation tranche

- Allocate admitted liveness in/out, definition, and use bit matrices at their
  exact capped sizes instead of growing them one cell at a time.
- Preallocate the initial block worklist and queued bitmap, fill the worklist by
  index, and retain the existing top-cursor reuse discipline.
- Preserve the four-million-cell cap, incomplete-input rejection, visit budget,
  fact ordering, and public API while removing cumulative array-growth copies.
- Existing liveness propagation and fail-closed contracts cover behavior;
  verification intentionally not run under the user's no-verify instruction.

## Completed analyzer lookup/dedupe tranche

- Hoist immutable CFG successor lookup from the per-local liveness loop to one
  resolution per worklist visit.
- Remove the impossible worklist growth fallback and write into the free slot
  guaranteed by the queued bitmap and fixed block-count capacity.
- Replace MEXH006's repeated linear reported-name scan with dictionary
  membership while preserving first-occurrence warning order and payloads.
- Existing liveness and match-exhaustiveness contracts cover behavior;
  verification intentionally not run under the user's no-verify instruction.

## Completed OPTME001 canonical-line tranche

- Add line-owned OPTME001 collection/check kernels and retain source-taking
  compatibility adapters.
- Route the lint driver's canonical line snapshot through the combined
  same-file analysis, eliminating four redundant splits and three duplicate
  enclosure arrays per file.
- Preserve parser revision checks, same-file ambiguity behavior, diagnostic
  line numbers/order, and request-local snapshot lifetime.
- Retain only compact warnings across parsing, never the file-sized line view;
  parse failure and stale revision paths continue to suppress OPTME001.
- Route the repo-wide scanner through one combined index per file and add
  source/line collector plus full warning-payload parity contracts.
- Verification intentionally not run under the user's no-verify instruction.

## Completed signature/scope-allocation tranche

- Replace cumulative per-character parameter and identifier construction in
  const-reference lint with boundary tracking and one substring per result.
- Preserve nested delimiter handling, `mut` exclusions, parameter identities,
  and source finding order; add nested-type and long-name contracts.
- Delay MIR function snapshot construction until a function-scoped typed pass
  arm is selected; module passes allocate no unused function snapshot.
- Preserve stable pre-pass iteration and fresh pass instances for function
  adapters; verification intentionally not run under the user's no-verify
  instruction.

## Completed query outline snapshot tranche

- Build one request-local target-file snapshot containing lines and symbols
  from one read and one split.
- Project imports lazily from snapshot lines only after local lookup misses, so
  common local hits do not pay a second full scan or allocate import records.
- Reuse it across definition, hover, completion, type, and signature queries;
  keep imported-module parsing and precedence unchanged.
- Preserve empty-file behavior, duplicate import ordering, line numbers,
  stdout, limits, and exit codes without introducing persistent cache state.
- Add a source-snapshot projection contract and structural guards proving
  type/signature cursor paths consume snapshot lines rather than rereading.
- Verification intentionally not run under the user's no-verify instruction.

## Completed formatter space-normalization tranche

- Replace the fixed-point repeated-space `contains`/whole-string `replace`
  loop with one ASCII-space-run scan and a final fragment join.
- Return already-normalized lines unchanged and preserve
  tabs, all non-space spans, operator cleanup order, and final trimming.
- Add empty, normalized, leading/trailing, long-run, tab-adjacent, and
  idempotence contracts plus a source guard against restoring the loop.
- Verification intentionally not run under the user's no-verify instruction.

## Completed semantic-query call-index tranche

- Reuse one `OutlineSnapshot` per queried file instead of reopening and
  splitting source inside each `calls(...)` or `implements(...)` predicate.
- Deduplicate requested callees and build a request-local, collision-free
  function/callee match dictionary in one source-line walk.
- Reduce worst-case `calls(...)` work from O(S*C*N) scans and repeated line
  arrays to expected O(N*C + S*C) lookup work; lazily skip indexing when the
  target or an earlier predicate rejects every candidate.
- Preserve top-level-only function recognition, indent-zero body closure,
  duplicate-name union, raw comment/string matching, result order, and API.
- Add direct positive/negative, duplicate declaration, closure boundary,
  legacy exclusion, and source-topology contracts; verification intentionally
  not run under the user's no-verify instruction.

## Completed TYPE001 cursor-scan tranche

- Replace rejected-prefix suffix slicing with a two-argument `find` over the
  original line and an absolute cursor advanced by one byte.
- Build the four ordered nonexistent-type search needles once per lint request
  rather than once per physical line.
- Reduce adversarial rejected-prefix scanning and copied bytes from O(N^2) to
  O(N) per bad name without changing whole-word boundaries.
- Preserve one warning per bad name per line, canonical bad-name diagnostic
  order, comment suppression, TYPE002 behavior, messages, hints, and API.
- Add prefix-heavy, repeated-exact, reverse-source-order, and source-topology
  contracts; verification intentionally not run under the user's no-verify
  instruction.

## Completed canonical-module call-index tranche

- Build one compact internal function-name-to-SymbolId dictionary during the
  existing ordered nonempty/unique validation pass.
- Replace every direct-call full-module rescan and temporary candidate array
  with expected constant-time dictionary resolution.
- Cache only successfully closed and pure callee names so repeated calls do not
  repeat region-manifest serialization and hashing; never cache failures.
- Reduce expected structural validation work from O(F^2 + C*F + repeated
  callee bytes) to O(F+C+unique referenced callee bytes), plus name-byte
  hashing/comparison, with O(F+U) compact request-local entries.
- Preserve owner/name/callee diagnostic precedence, exact messages, recursive
  skipping, instruction order, hashes, and public APIs.
- Add repeated-pure-leaf, missing/duplicate precedence, exact effect rejection,
  and source-topology contracts; verification intentionally not run under the
  user's no-verify instruction.

## Completed native-build sparse-diagnostic tranche

- Replace full stderr `split("\n")` with an absolute newline cursor, match on
  source byte ranges, and materialize only retained lines.
- Append only matching diagnostic lines through the unique result owner;
  retain no array of noise-line fragments.
- Reduce auxiliary failure-path peak storage from O(N+L) projected stderr bytes
  and line slots to O(D+M), retained diagnostics plus the longest line.
- Preserve native byte text, diagnostic order/count, broad matching,
  empty/trailing behavior, full-stream spill, head/tail excerpts, banners, and
  APIs; avoid the interpreter split indentation-loss defect.
- Add exact sparse/empty/no-match behavior and source-topology contracts;
  verification intentionally not run under the user's no-verify instruction.

## Completed STUB003 candidate-gate tranche

- Add an allocation-free byte scanner for `pass_todo` in the virtual stream
  produced by deleting exactly ASCII space and tab.
- Run the historical two-replacement normalization and four exact STUB003 shape
  checks only on candidate lines.
- Remove Θ(B) common-case normalized-copy bytes while retaining linear scanning
  with a fixed nine-byte token.
- Preserve split spellings, comments/strings, Unicode whitespace behavior,
  production/test suppression, diagnostic count/message/fix, and STUB003-before-
  T001/D001 ordering.
- Add direct gate, production/test, ordering, Unicode-whitespace, and source-
  dominance contracts; verification intentionally not run under the user's
  no-verify instruction.

## Completed check-tier accumulator tranche

- Replace input-sized keyword, module-tier, and restricted-file copy-on-append
  operations with unique-owner `push`, preserving stable encounter order.
- Count default full-tier files instead of retaining paths that are never
  checked, reducing peak path storage to seed/core subsets.
- Build ordered operator tables once per checked file and share them read-only
  across line checks; retain the source-taking compatibility adapter.
- Replace per-byte stripped-source concatenation with one byte scan, unchanged
  code spans, one mask fragment per string, and a final join.
- Replace the punctuation replacement chain plus split with one byte-indexed
  maximal-word span collector using the exact legacy delimiter set.
- Build one minimum-required-tier dictionary per request and reuse it across
  files instead of linearly rescanning keyword arrays twice per word.
- Add guards for owner mutation, full-tier count-only storage, direct operator
  literals, per-file pattern reuse, span-owned string/comment masking, and
  replacement-free keyword extraction, plus direct delimiter, duplicate-tier,
  and ordering cases.
- Verification intentionally not run under the user's no-verify instruction.

## Reviewed workspace JSON process tranche

- Rejected the direct parent-lint shortcut after parallel review found trace
  stdout could corrupt JSON and private lint-tier state could leak across calls.
- First add a nonprinting structured lint API and lint-owned, cleanup-safe state
  boundary; then add behavioral parity/isolation fixtures.
- Retain `2N` explicit per-file process behavior until those safety gates exist;
  the target remains a serial request-owned compiler session with zero children.
- Track the blocker in
  `doc/08_tracking/bug/workspace_diagnostics_nested_process_overhead_2026-08-22.md`.
- Verification intentionally not run under the user's no-verify instruction.
# Completed tranche: predicate-promotion quarantine (2026-08-24)

- Marked `PredicatePromote` disabled with an explicit sole-use/dominance/span
  reason and removed its active witness registration.
- Converted module, function, and block adapters to constant-time identity
  paths, closing direct-call bypasses and disabled-pass allocation overhead.
- Removed the stale `simple-predicate-promote` backend/JIT recommendation so
  facts or profile hotness cannot advertise a disabled transform.
- Replaced positive fusion assertions with quarantine oracles, including the
  later-mask-use witness that would previously create undefined-local MIR.
- Updated descriptor expectations and the generated/manual evidence companion.
- Parallel compiler audit supplied the defect and reactivation contract;
  semantic, performance, and fixture reviews are required before sync.
- No manual verification was run under the user override.
# Completed tranche: watch dependency normalization hoist (2026-08-24)

- Extracted exact changed-path normalization behind a single helper.
- Precomputed one normalized text per changed file before graph/import scans.
- Preserved the compatibility matcher, graph order, duplicate behavior, prefix
  handling, and order-sensitive self/dependency behavior.
- Added one canonical executable spec and manual for matching and ordering
  oracles without creating a legacy shadow copy.
- Recorded the allocation reduction separately from the unchanged nested-search
  complexity; no runtime speedup or RSS claim is made without measurement.
- Parallel performance audit supplied the defect and bounded patch contract;
  semantic, performance, and fixture reviews remain required before sync.
- No manual verification was run under the user override.
# Completed tranche: Any-audit linear text and bounded totals (2026-08-24)

- Replaced per-character immutable prefix growth with fragments plus one join.
- Replaced per-occurrence prefix reconstruction/trim with bounded index checks.
- Preserved column blanks, comments, keyword boundaries, nesting, precedence,
  and classification order.
- Replaced retained all-site aggregation with class counters and one site count.
- Extended the existing canonical/legacy fixture pair and added a canonical
  manual covering exact sanitizer and long-prefix behavior.
- Runtime timing/RSS evidence remains unavailable under the no-verification
  override; only source-level complexity and retained-data bounds are claimed.
- Parallel semantic, performance, and fixture review remains required.
# Completed tranche: MEXH sibling boundaries and source spans (2026-08-24)

- Added an exact sibling-arm indentation boundary to the query lint fallback.
- Prevented multiline bodies, nested cases, blanks, and comments from mutating
  wildcard/pattern/arm-count state.
- Preserved MEXH004 precedence and semantic-lint behavior.
- Extended the JSON emitter with explicit one-based start/end columns for arm
  and match-level MEXH001-005 diagnostics.
- Extended canonical/legacy fixtures and the manual with multiline, nested,
  later-sibling, and exact-span oracles.
- No manual verification was run under the user override; parallel semantic,
  performance, and fixture review remains required.

# Completed tranche: quarantine unsupported filesystem hints (2026-08-24)

- Reclassified write coalescing and syscall batching as analysis-only.
- Removed executable construction of backend-unsupported hint intrinsics.
- Preserved candidate counters for future remarks and rehabilitation.
- Updated canonical/legacy direct-adapter oracles and recorded-dispatch oracles
  to require unchanged MIR and explicit analysis-only disposition.
- Source-level complexity improves from block scans plus rebuilt instruction
  arrays to constant-time adapter return; candidate analysis remains opt-in.
- No manual verification was run under the user override; static parallel review
  is required before the unverified sync.

# Completed tranche: linear semantic duplicate buckets (2026-08-24)

- Replaced comma-separated index strings with stable bucket IDs and nested
  integer arrays in the local semantic analyzer.
- Removed repeated decimal formatting, growing-prefix copies, split substring
  allocation, and integer reparsing.
- Saturated unconditionally skipped common-token buckets at the 401-member
  sentinel rather than retaining every later document index.
- Preserved membership order, oversized-bucket policy, pair deduplication,
  similarity thresholds, match construction, and final sorting.
- Existing cross-directory and exact-one same-file semantic fixtures remain the
  behavioral oracles; no alternate implementation or foreign-language path was
  introduced.
- Source-level bound changes from quadratic copied character payload per hot
  token to amortized linear membership insertion. No timing/RSS claim is made
  because manual verification remains disabled by user instruction.

# Completed tranche: UNUSED001 sibling scope and spans (2026-08-24)

- Bounded each text-fallback function by its own header indentation.
- Prevented sibling class methods from contributing identifier uses to one
  another's unused-variable decision.
- Preserved nested body lines and blank-line behavior.
- Derived JSON columns from the original indented declaration line.
- Added paired executable oracles and a canonical manual for sibling isolation
  and exact one-based start/end columns.
- No manual execution was run under the user override; static semantic,
  performance, and evidence review is required before sync.

# Completed tranche: linear feature usage index (2026-08-24)

- Replaced growing immutable Markdown prefixes with fragments and one join.
- Replaced dictionary-held growing arrays with stable bucket IDs and indexed
  nested-array mutation.
- Preserved first-category order, within-category feature order, status/ID
  defaults, describe/test counts, output path, and Markdown schema.
- Replaced whole-path splitting with one last-slash slice.
- Added paired rendering/path oracles and a canonical manual.
- No manual execution was run under the user override; static semantic,
  performance, and fixture review is required before sync.

# Completed tranche: requested-line DEPR002 projection (2026-08-25)

- Added a bounds-safe scalar lexical projection that scans only through the
  requested line while preserving multiline triple-string state.
- Removed whole-file DEPR002 arrays and all-line trim loops from both code-action
  owners; each now directly inspects one validated target.
- Preserved exact DEPR002/DEPR003 output and original byte columns.
- Added paired prefix-state, bounds, exact-column, and owner-wiring evidence and
  refreshed the canonical manual.
- Static target: O(B<=r + R) postprocessing and O(1) auxiliary storage beyond
  split lines; no manual execution or timing/RSS measurement was run.

# Completed tranche: flat-bridge string construction (2026-08-24)

- Added no-brace and no-doubled-brace identity paths for non-raw literals.
- Replaced per-character immutable decoder prefixes with ordinary-run fragments
  and one join.
- Replaced interpolation-body prefix concatenation with fragments and one join.
- Preserved raw bypass, invalid-fragment fallback, escape order, and MIR
  interpolation ownership.
- Added paired exact semantic and structural fixtures plus a canonical manual.
- Static target: remove O(S²) and O(K²) copied bytes; no execution or
  performance/RSS measurement was run under the user override.

# Completed tranche: UNREACH001 lexical successors (2026-08-24)

- Extended the shared successor index with executable-line, lexical-return, and
  exact token-span facts.
- Excluded comments, strings, and triple-string payload from return origins and
  successor selection.
- Routed live query lint and collected query-check JSON through identical facts.
- Preserved the linear reverse-stack algorithm and RET001 fact reuse.
- Added paired false-positive, successor, exact-span, index, and routing evidence
  plus a canonical manual.
- No manual execution or timing/RSS measurement was run under the user override.

# Completed tranche: DEPR001 lexical facts (2026-08-25)

- Replaced trimmed raw-text DEPR001 matching with stateful original-byte facts.
- Excluded comments and ordinary/triple-string payload while resuming after
  closures.
- Preserved every real same-line match and exact message/severity ordering.
- Added true identifier boundaries and original one-based exclusive spans.
- Reduced allocation from per-byte/per-token substrings to accepted names only.
- Added paired ordered-fact, decoy, exact-JSON, and structural evidence plus a
  canonical manual.
- No manual execution or timing/RSS measurement was run under the user override.

# Completed tranche: MIR local binding index (2026-08-24)

- Retained the staged-native-safe parallel binding arrays as authority.
- Added a flat primitive-slot open-address index with geometric growth below
  70% load for expected constant-time bind and lookup.
- Wired the sole constructor, common per-function reset, and both lambda scope
  snapshot/restore sites in lockstep.
- Added paired collision, resize, update, miss, rollback, reset, and lifecycle
  evidence plus a canonical manual.
- Performance target: replace O(L^2 + R*L) comparisons with expected O(L+R)
  operations while accepting O(L) additional flat index storage.
- No manual execution or performance/RSS measurement was run under the user
  override.

# Completed tranche: doc-coverage single-scan reporting (2026-08-24)

- Replaced normal-report grep pipelines with Pure Simple recursive file facts.
- Preserved public/documented definitions and overlapping `-B2` docstring-line
  deduplication.
- Added a request-local distinct-root cache while preserving duplicate requested
  root multiplicity and std/lib shared facts.
- Kept one file content live at a time and removed captured grep output from
  terminal, JSON, and Markdown reporting.
- Added mirrored semantic/cache/process-absence evidence and a canonical manual.
- No manual execution, timing, subprocess, byte-read, or RSS measurement was run
  under the user override.

# Completed tranche: PatternIdiom safety quarantine (2026-08-24)

- Marked PatternIdiom Disabled and removed its executable witness claim.
- Made every production PatternIdiom adapter an exact identity.
- Retained rewriting under explicit candidate-only names for parity fixtures.
- Replaced x86-64's unsupported-intrinsic NOP fallback with closed-allowlist,
  fail-loud handling.
- Updated paired fixtures and canonical manuals to separate production
  quarantine evidence from candidate simulation.
- Performance review: normal builds avoid candidate traversal; no runtime/RSS
  measurements were run under the user override.

# Completed tranche: DEPR002 lexical/span hardening (2026-08-24)

- Extracted position-preserving string/comment masking into a small shared
  source-fact module.
- Routed query lint diagnostics, JSON collection, and both code-action paths
  through one `deprecated_new_column` helper.
- Preserved original indentation in one-based JSON start/end columns.
- Added paired executable lexical/span fixtures and a canonical manual.
- Performance review target: one linear byte scan per inspected line, no parser,
  no full tier-check dependency, and no repeated prefix construction.
- No manual execution or measurement was run under the user override.

# Completed tranche: LLVM-direct minimal C construction (2026-08-24)

- Added a pure text-to-text core beneath the existing file adapter.
- Replaced repeated array membership with a dictionary-backed seen set while
  preserving first-seen function order.
- Excluded generated-shell `main` from helper storage without changing bytes.
- Replaced growing immutable C prefixes with complete fragments and one join.
- Added canonical exact ordered, main-presence, empty-input, adapter, and
  structural regression oracles plus a manual.
- No manual execution or performance/RSS measurement was run under the user
  override.

# Completed tranche: SAFE001/SAFE003 lexical hardening (2026-08-24)

- Added a bounded multi-pattern, stateful code-only projection with original
  source columns.
- Routed unsafe-scope state, SAFE001 assembly detection, and SAFE003 pointer
  detection through one request-local fact array.
- Replaced the single unsafe-indent slot with a nested indentation stack and
  rejected unsafe-prefixed ordinary identifiers as scope markers.
- Rejected comment/string/docstring false positives and fake unsafe-state
  transitions while preserving real unsafe suppression.
- Replaced line-wide JSON locations with exact first-token spans.
- Added canonical severity, lexical-boundary, scope, precedence, and span
  evidence plus a manual.
- No manual execution or runtime/RSS measurement was run under the user
  override.

# Completed tranche: linear app feature index (2026-08-24)

- Replaced growing app-index Markdown prefixes with fragments and one join.
- Replaced whole-path splitting with a final-slash basename slice.
- Preserved exact bytes, input order, nested behavior counts, status fallback,
  output path, table framing, and final newline.
- Added paired exact nonempty/empty/path oracles and a canonical manual.
- No manual execution was run under the user override; static semantic,
  performance, and fixture review is required before sync.
