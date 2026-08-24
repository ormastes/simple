# Compiler Performance Diagnostics

## Operator contract

Simple separates four evidence tiers:

1. `simple check`: high-confidence typed source diagnostics.
2. optimized builds with performance remarks: safe transforms and exact missed reasons.
3. `simple perf --deep`: bounded interprocedural cost and memory summaries.
4. `.sprof` evidence: ranking by observed hotness, cardinality, allocation, and copy bytes.

Source warnings describe likely application defects. Optimizer remarks describe compiler
decisions. Runtime profiles rank candidates but never authorize a semantics-changing
transformation.

Collection rules use the `collection_performance` configuration name. SDN entries and
`@allow`/`@warn`/`@deny` attributes resolve lint names without rebuilding the registry per
name, so large explicit configurations do not multiply registry allocation and scanning.
Effective default levels are likewise built once per configuration/profile change rather
than once per diagnostic; file-level policy lookup is allocation-free.
Within one lint request, the target `simple.sdn` is parsed once and its resolved policy is
reused by source and parsed-AST rule projections. A path mismatch forces fresh resolution.
Each diagnostic resolves suppression and effective severity together; evidence-tier caps
therefore require one stable-code mapping and one configuration lookup.
Combined source and parsed-AST lint phases share one request-local line view and release it
after projection, avoiding duplicate source splitting without retaining editor contents.
The same view feeds file attributes and migrated line-oriented rules; compatibility source
wrappers remain for standalone callers.

The first typed collection-analysis slice is request-local `HirPerfFacts`. Its
COLL002 projection requires a resolved method symbol, authoritative typed array/slice
receiver, verified version-matched linear-cost metadata, and positive loop ancestry.
Unknown or unverified facts produce no typed warning and no fix. Until the standard-
library registry and driver adapter land, existing source-pattern collection warnings
remain advisory compatibility output rather than typed proof.

## Optimizer truth

The requested pipeline is an inventory. The effective pipeline contains only descriptors
whose `PassStatus` is `Active`. `AnalysisOnly`, `RemarkOnly`, `Skeleton`, and
`Disabled(reason)` entries remain visible but cannot enter transformation dispatch.

Every active transform must have a positive sentinel, negative legality fixture,
idempotence check, IR verification, and semantic differential evidence. Missing facts,
timeouts, or unavailable backends fail closed.

The registry now gives each admitted transform a stable positive and negative witness ID.
The first contracts are `pattern.supported_aes_call`,
`predicate.mask_cmp_masked_add`, `fs.two_stores_same_base`, and
`fs.two_calls_same_callee`, paired with explicit non-candidate witnesses. An `Active`
descriptor without a complete witness contract is a compiler-integrity error.

`optimizationpipeline_report_json` emits deterministic planning evidence under schema
`simple.opt-pipeline-report/v1`. Each requested ordinal records pass status,
expectation, backend outcome and reason. Planning is not execution: its run outcome is
`not-run` and execution counters are `null`. Consumers must not infer that a pass ran or
changed MIR from selection alone. Populated `PassRunRecord` counters will be admitted
only after dispatch owns verified change receipts.

The first recorded execution boundary is `run_named_pass_with_record`. It rejects an
invalid input or output when block/local identity, entry membership, or CFG targets are
malformed. The active `write_coalesce` and `syscall_batch` function adapters report exact
native candidate/transformed counts from the hints actually emitted, stable witness
reasons, and instruction deltas. The recorded path no longer performs a separate
candidate-count scan before the rewrite. The boundary rejects disagreement between
native outcomes and serialized MIR change. It
never substitutes `candidates=1` merely because a function changed, and a newly active
function pass without an exact outcome adapter fails closed. This is a
structural receipt with indexed identity, CFG-target, canonical access-coverage, and
declared operand/local checks plus exact function ABI-local type checks, but not yet proof
of opcode type correctness, SSA dominance, ownership, or
semantic equivalence; those omissions remain explicit blockers for `--verify-each`.
CFG terminator edges are checked in place against the indexed block set; verification does
not allocate a target collection per basic block, including high-fanout switches.
Verifier consumers should key automation on stable `MIRV001`-`MIRV019` codes, not message
text. `MIRV999` means the failure remains fail-closed but its machine category has not yet
been admitted.
Module receipts aggregate function receipts in sorted symbol order and add `MIRVM001` for
function-map key/symbol disagreement. They do not imply that a module optimization ran.

## Diagnostic policy

`COLL*` findings belong to the `collection_performance` lint family. Moderate and strict
profiles warn; robust and critical profiles may deny typed high-confidence findings.
The AST compatibility analyzer carries an explicit `source-pattern` evidence tier,
caps itself at warning even under `--deny-all`, marks findings uncertain, and never
attaches a machine-applicable fix. Missing uncertainty text is not treated as proof;
only an explicit `typed-proven` tier authorizes escalation. Typed HIR or
CollectionPlan analysis may offer a fix only after receiver semantics, effects, aliasing,
mutation version, ordering, and lifetime are proven.

Human and JSON records preserve stable code, location, confidence, evidence, uncertainty, hint, and
optional proof-gated fix. Unknown rule codes remain visible rather than silently
suppressed.

Fallback source locations are indexed once per source view. Standalone lint reuses that
index for collection and wildcard-export findings, while query/LSP reuses its already split
lines for callable, wildcard, and GC-boundary import locations. These are compatibility locations, not typed
proof: exact AST or HIR causal spans remain the target, and fallback recovery never
authorizes a transform.

The compatibility `UNUSED001` producer partitions functions once and builds one
function-local identifier-frequency table. It deliberately retains text semantics
(including words in comments and strings) until typed HIR use-def facts own the rule,
but it does not rescan the entire function for every declaration.

The compatibility `RET001` producer computes last-statement facts once with a
reverse monotonic indentation stack. Candidate calls consume an indexed Boolean
instead of rescanning their remaining source suffix, keeping deeply nested files
linear in line count. The same caller-owned fact record supplies the exact next
same-or-shallower source line to `UNREACH001`, so return diagnostics do not rebuild
or rescan indentation facts per rule.

The compatibility `CLOS001` producer indexes visible outer-variable names and extracts
one leading assignment target per closure-body line. It therefore avoids comparing every
body line with every captured name; lexical capture truth still belongs to typed HIR.

Textual match compatibility facts retain ordered variants and arms for stable messages,
alongside dictionary membership for duplicate and missing-variant queries. Type inference
still fails to a generic advisory when patterns do not identify exactly one enum; typed
scrutinee facts are required before increasing confidence.

The standalone CLI and query/LSP source-pattern collection projections use the same
confidence vocabulary. Query governance recognizes `COLL001` through `COLL019`, so
`Allow` suppresses them, while robust/critical policy cannot upgrade those untyped
findings to errors. Severity projection is metadata-only and adds no parse or scan.

## Shared facts

`PerfFacts` is the function-local owner for reusable MIR analysis. Its deployed slices
own CFG successors/predecessors, block indexes, reverse-postorder, immediate dominators,
a linear def/use index, and block live-in/live-out facts. Def/use buckets are indexed through declared locals and are
mutated in place during one traversal, avoiding definitions-by-uses scans and repeated
copy-on-write rebuilding. Any unmodeled instruction or undeclared local reference marks
the def/use view incomplete; consumers must fail closed.

Liveness uses flat dense bit matrices indexed by block and declared local, avoiding nested
array COW during fixed-point propagation. A predecessor worklist reuses its storage, has
an explicit visit budget, and rejects functions above the dense-cell memory cap before
allocating the matrices. Duplicate blocks, dangling CFG targets, uncovered opcodes,
unknown locals, or budget exhaustion make liveness explicitly incomplete. A
`CallTerminator` result with an unwind edge is conservatively not treated as a block-wide
kill because it exists only on the normal edge.

The canonical access visitor explicitly models ownership, async, probes, pipeline,
SIMD/warp, GPU, VHDL, nested-place, and inline-assembly operands. Assembly outputs must
name locals. Result-match ghost metadata, text-encoded GPU launch arguments, and hidden
VHDL process-body CFG edges still make the facts incomplete; no liveness consumer may
guess through those cases. Dormant DCE also conservatively retains every newly modeled
effectful family.

A registry-backed unit contract compares the named access arms against the generated
`MirInstKind` registry and rejects wildcard coverage. Adding a new opcode therefore
requires an explicit access decision rather than silently inheriting a default.

Every pass has an explicit preservation contract. Current transforming adapters
conservatively invalidate CFG, dominance, def/use, and liveness; non-transforming statuses preserve
them. Finer preservation can be admitted only with a focused witness. Loop forest,
range/induction, region alias, effects, and MemorySSA-lite remain future slices of the
same revision-local owner.

The dormant DCE implementation now consumes shared reachability and liveness, seeds each
block from live-out plus terminator uses, and performs one backward instruction transfer.
Its former private CFG traversal and per-definition later-instruction scans are removed.
DCE remains `Skeleton`: opcode effect/trap coverage, full verification, and semantic
differential gates are still required before its public adapter may transform MIR.

Natural-loop membership is built from dominance-proven latch edges by a reverse
predecessor walk bounded at the header. Multiple latches are unioned once and bodies are
emitted in stable MIR order. This avoids the former per-header forward/backward CFG
traversals and, critically, prevents an inner loop from absorbing outer-loop blocks merely
because both belong to the same strongly connected region. Canonical nesting, preheaders,
dedicated exits, and SCEV-lite are still pending shared facts.

The vectorizer projects loop-local chains from shared complete `PerfFacts`; it rejects
the candidate when opcode or local coverage is incomplete. Its compatibility operand and
array-access collectors append into owned buffers, and dependency summaries use linear
extrema/adjacent relations rather than definitions-by-uses Cartesian enumeration.
These compile-time improvements do not change its `AnalysisOnly` status: alias, memory,
effect, induction, target, and semantic differential proofs remain incomplete.

Typed-storage production and storage-layout access summaries also consume the shared use
index. A function is indexed once, rather than rescanned for every projection candidate;
unknown opcode/local coverage rejects storage rewriting and prevents a partial use count
from being interpreted as single-use ownership evidence.

The standalone lint compatibility path builds one fallback source-location index for
function declarations and unique collection-fix lines. It no longer rescans the whole
file for every COLL warning. This is a secondary improvement: repository measurements
still place the dominant cost in `parse_module_silent_checked`, and the architectural
fix remains reuse of the driver/LSP parsed and typed revision rather than another parser.

Compiler and LSP owners can now call `lint_cli_source_with_parsed_revision`. Its
`LintParsedRevision` binds declaration indices to path, source SHA-256, and AST arena
generation; a mismatch produces deny-level `LINTREV001` and runs no AST rule. The
standalone command retains its one parse for compatibility, then delegates to the same
parsed-results function. This bridge removes the need for a second lint parse when a
caller already owns the exact live revision; driver/LSP wiring and measured latency
evidence remain pending.

The query/LSP AST compatibility projection also uses the checked parser verdict. A
parse failure emits deny-level `PARSE001` with `NOT LINTED` wording instead of returning
a false clean result, the caller's prior parser-error state is restored, and the redundant
pre-parse AST reset is gone because parser initialization owns that reset. Its legacy
`COLL*` source-pattern records are always warnings and explicitly disclose that receiver
type, effects, aliasing, and mutation version are unresolved. This containment does not
make those findings typed or authorize fixes.

## Current safety containment

- Unknown escape state remains escaping after finalization.
- Auto-vectorization is analysis-only; candidate recognition requires an exact integer
  unit step found in the actual loop header/direct body region.
- Canonical `collection_opt` dispatch is disabled. Retained patterns do not yet prove
  ownership/COW equivalence, alias and memory versions, call effects,
  trapping/allocation behavior, or destruction order.
- Collection hoisting remains inert until it can target a true preheader with complete
  dominance, effects, alias, zero-trip, and speculatability proofs.
- Loop trip counts remain unknown until SCEV-lite proves the complete recurrence.
- Dormant identity and proof-incomplete transforms are absent from effective pipelines.
- Inline facades and target narrowing are classified `Skeleton`; read-ahead hoisting is
  `AnalysisOnly`. Their presence in a requested pipeline is never transformation proof.
- General fusion, stack promotion, general LICM, BCE, GVN, string-builder rewriting, and
  TCO remain unavailable until their proof contracts pass.

See [the architecture](../../04_architecture/simple_compiler_performance_memory_efficiency.md)
and [system-test plan](../../03_plan/sys_test/simple_compiler_performance_memory_efficiency.md).
## Checked MIR pass execution

Set `SIMPLE_MIR_VERIFY_EACH=1` to apply the admitted structural MIR proof surface to the
module before and after each canonical optimization pass. Malformed input or output is
rejected fail-closed; tracing with `SIMPLE_COMPILER_TRACE=1` reports the stable verifier
codes. The admitted proof includes single-definition and dominance-scoped SSA use checks.
It also validates exact destination/source contracts for constants, copies/moves, and
casts/bitcasts. Receipt checked/unproved counters disclose partial type coverage. It does
not yet prove all opcode types, ownership, or loop invariants.

Verification is intentionally opt-in. The setting is cached after its first lookup, so
normal builds do not scan MIR or allocate verifier receipts. Enabled verification scans
the module and sorts function symbols for deterministic evidence, and should therefore
be used for compiler development and focused diagnostics rather than routine builds.

Lint source is split into lines once per request. Traceability, SPipe-quality, typed-UI,
file-policy, and other line-oriented checks share that immutable view; rule owners must
not create private full-source line arrays. This bounds transient memory while preserving
the same diagnostic ordering and locations.

The lint driver calls the EasyFix registry once. Individual registry rules are not
re-invoked by the driver; this prevents duplicate source scans, diagnostics, replacement
objects, and later fix-policy work.

For spec files, the EasyFix registry derives line number, byte offset, trimmed text, and
indent once per source line and shares those contexts across SPipe rules. Non-spec files
do not allocate this context array. Compatibility calls outside the compiler may build a
private view, but the normal lint path always supplies its existing canonical lines.

The same request-owned contexts feed general code, annotation, deprecation, and module
boundary EasyFix rules. Duplicate-typed-argument candidates reuse canonical lines rather
than allocating one line array per signature. These facts are immutable and released with
the registry call; long-lived lint/LSP instances retain no EasyFix source view.

Compiler-owned EasyFix rules—including import, API-width, primitive/bool, grammar, and
script policy checks—consume that same view. Compatibility calls test path eligibility
before constructing private lines. File-level allow scanning also reuses the caller's
lines, so suppression does not add a hidden full-source array.

`std.tooling.easy_fix.rules_helpers` owns the canonical EasyFix source view and line
context type. Compiler helpers re-export it rather than defining another representation.
Contextual-keyword, deprecated syntax, stub, and compiler rules therefore share one
request-scoped context array with identical byte-offset semantics.

Duplicate-typed-argument fixes index unique function-name/arity targets and scan source
call sites once. Ambiguous overloads remain untouched. Replacements retain declaration
grouping and source order; memory grows with candidates and emitted replacements rather
than candidate count multiplied by source lines.

EasyFix policy uses the semantic code extracted from either `L|E:code:location` or
`direct_code:location` IDs. Direct warning IDs such as W0406 remain W0406; their line is
never interpreted as a code. Known annotation membership uses allocation-free exact
dispatch rather than rebuilding whitelist arrays for each source line.

EasyFix diagnostics participate in the same configurable policy as native lint records.
Existing named rules such as export boundaries, SPipe quality, resource leaks, stubs, and
annotations map directly to their configured names; W0406 uses `visibility_boundary`.
Default deny and authored allow settings therefore apply consistently after ID decoding.

Contextual-keyword, deprecated syntax, struct-construction, short-grammar, raw-unit, and
SIMD EasyFix advice is configurable and defaults to warning. The four short-grammar
diagnostic codes share the `short_grammar_refactor` policy name.

Source-only annotation checking reports `unknown_annotation`, because raw `@name` syntax
cannot distinguish decorators from attributes. It accepts the union of known names and
emits at most one warning per line. Existing `unknown_decorator` and `unknown_attribute`
settings remain aliases for compatibility; typed analysis may later provide precise
category-specific diagnostics.

Collection loop-invariant hoisting is disabled and contains no dormant header-rewrite
body. The compatibility entrypoints return the original blocks. A future implementation
must consume a real preheader plus dominance, alias/memory, effects, zero-trip, and
speculatability proofs; analysis-only scalar predicates do not authorize movement.
