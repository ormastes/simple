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
native candidate/transformed counts, stable witness reasons, and instruction deltas;
the boundary rejects disagreement between those counts and serialized MIR change. It
never substitutes `candidates=1` merely because a function changed, and a newly active
function pass without an exact outcome adapter fails closed. This is a
structural receipt, not yet proof of SSA dominance, type correctness, ownership, or
semantic equivalence; those omissions remain explicit blockers for `--verify-each`.

## Diagnostic policy

`COLL*` findings belong to the `collection_performance` lint family. Moderate and strict
profiles warn; robust and critical profiles may deny typed high-confidence findings.
The AST compatibility analyzer caps itself at warning, marks findings uncertain, and
never attaches a machine-applicable fix. Typed HIR or
CollectionPlan analysis may offer a fix only after receiver semantics, effects, aliasing,
mutation version, ordering, and lifetime are proven.

Human and JSON records preserve stable code, location, evidence, uncertainty, hint, and
optional proof-gated fix. Unknown rule codes remain visible rather than silently
suppressed.

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
