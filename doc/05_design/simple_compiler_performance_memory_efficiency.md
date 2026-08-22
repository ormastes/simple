<!-- codex-design -->
# Simple Compiler Performance and Memory Efficiency — Detail Design

## Scope

This design implements REQ-001..REQ-025 and NFR-001..NFR-015 as one staged program. It does not claim implementation or verification completion.

## Data model

### Pass integrity

`MirPassDescriptor` gains status, expectation, delegation, required/preserved/invalidated facts, and stable identity. Registry construction validates combinations. `EffectivePipelinePlanner` resolves names and backend policy before execution. Each pass returns `PassOutcome` containing original-or-new MIR, `MirChangeReceipt`, `PassRunRecord`, and verifier receipt when required. No partially mutated MIR escapes a failure.

Compiler self-rules include identity/empty active wrapper, missing/unchanged sentinel, invalid contract, dishonest effective listing, duplicate identity, missing run evidence, unenforced required fact, missing verifier receipt, and nondeterministic report order.

The verifier is admitted incrementally by named proof surface. The current
`MirStructuralVerificationReceipt` proves block/local identity, canonical access coverage,
declared operand/local membership, signature-consistent ABI locals, entry membership, CFG
target closure, single-definition SSA shape, and definition-before-use dominance. It must
never be labeled a general MIR or semantic verifier.
The current partial opcode-type slice covers `Const`, `Copy`/`Move`, and `Cast`/`Bitcast`
and reports checked/unproved instruction counts. Later receipts add remaining opcode type
rules, ownership, loop-boundary,
and semantic-differential evidence. A pipeline-wide `--verify-each` claim requires all
applicable receipts, not merely the structural slice.
The receipt exposes parallel stable `MIRVnnn` codes and human messages; cardinalities
must match, and unclassified future failures use the explicit `MIRV999` sentinel.
The module receipt visits sorted function symbol IDs, checks map-key identity, aggregates
child proof surfaces and counts, and remains separate from module-pass execution evidence.

### Typed diagnostics

`PerfFactCollector` visits typed HIR once and indexes events by function, loop, call, receiver, value, region origin, and source span. Rules query indexes and `OperationSummaryRegistry`; they never reparse or recursively traverse the module independently.

`PerfRuleRegistry` owns stable code, group, tier, default kind/policy, fix support, and suppression. `PerfDiagnostic` projects to legacy V1 only for compatibility-owned rules and to deterministic V2 text/JSON/LSP. Exact source origin is mandatory; textual location recovery is removed per migrated rule.

Configuration-name membership must not allocate the complete registry for every SDN or
attribute entry. `all_lint_names` remains the enumeration surface; the hot parser path
uses allocation-free `lint_name_is_known` dispatch. A parity fixture prevents drift.

Effective default levels are immutable configuration state. Construct them once per root
configuration/profile change and share them with child configs; never rebuild profile
dictionaries from `get_level` per diagnostic. Overrides remain a separate small map.

Project policy reuse is provenance-bound. `LintConfig.source_path` names the exact parsed
manifest. A `Linter` may retain one last resolved `(file path, config)` pair for the
immediately following parsed-rule projection; the next file overwrites it. Broader caches
must add size/mtime or content-digest invalidation before admission.

Suppression and severity projection are one decision. `LintPolicyDecision(keep, level)`
maps the stable code and reads effective configuration once, then applies the evidence-tier
cap. Producers must not independently call keep and level APIs for the same diagnostic.

The source-line view is request-scoped. Combined text/EasyFix plus parsed-AST lint may
retain one COW line array between the two synchronous phases. Every success, parse error,
revision mismatch, and non-Simple early exit releases it. Ordinary lint calls retain none.

Line-oriented rule APIs expose `*_lines` consumers plus compatibility string wrappers.
The canonical lint owner passes one immutable/COW view through config and rule consumers;
only standalone external wrappers may split independently. Rule order remains unchanged.

During compatibility migration, `LintDiag.evidence_tier` is the single severity
input shared by CLI and query/LSP projections. `SourcePattern`,
`ParsedStructural`, and `Incomplete` performance diagnostics are warning-capped;
`TypedProven` follows profile policy. Human and JSON output carry the same stable
confidence, evidence, and uncertainty fields. The projection does no source read,
parse, hash, or tree traversal.

### Symbolic resources

`CostExpr` constructors flatten/sort/fold checked constants, cap depth/degree/variables/parts, and return `Unknown(BudgetExceeded)` rather than overflow. Expected, amortized, worst-case, total allocation, copied bytes, and peak-live bytes remain distinct.

`OperationSummary` covers receiver capability, time/resources, cardinality, access, order, uniqueness, laziness/enumeration, effects, and invalidation. Unknown user/foreign operations use top effects and unknown costs.

### MIR facts

`PerfFactsManager.for_function(MirRevision, MirFunction, AnalysisBudget)` returns a query facade. Fact construction is lazy and dependency-aware. Each result carries fingerprint, dependencies, counts, elapsed time, and budget. Cancellation is not cached; immutable incomplete results may be cached only for identical revision+budget.

CFG uses indexed successors/predecessors and cursor/deque worklists. Dominators use CFG order. LoopForest derives natural loops from dominance, retains multiple latches/exits, identifies irreducible loops, and never equates bound with trip count. Def-use includes terminators/phis; liveness uses bitsets; range proofs are dominance/program-point scoped. MemorySSA-lite versions regions and makes unknown writes clobber possibly aliased regions.

### Escape and COW

Escape finalization keeps unresolved sites `Unknown/MayEscape`. Production terminators/calls/stores/captures/suspensions feed proof paths. Field identity is base region + field, not guessed type/local. Stack eligibility requires closed flows, static/bounded size, alignment, frame budget, lifetime endpoint, and target policy.

Proposed COW MIR operations expose ensure/clone/mutate sites. Uniqueness transfer handles moves, aliases, calls, captures, returns, and joins. Profile counters share stable site IDs but cannot prove uniqueness.

## Rule evaluation

Tier 0 runs known high-confidence typed rules and suppresses fixed-small or unknown cases. Tier 1 adds MIR legality and remarks. Tier 2 uses bounded SCC summaries/affine solving and reports incomplete. Tier 3 correlates optional profiles.

Lint revision reuse is capability-bound, not a raw `[DeclId]` API. A
`LintParsedRevision` carries path, source digest, AST arena generation, and declarations.
The parsed lint entry checks all three identity dimensions before reading arena indices;
stale identity is a deny diagnostic, never a fallback parse or silent empty result.
Standalone lint owns exactly one parse and then calls the same parsed-results owner.

Fix applicability:

- Reserve and duplicate-lookup fixes require exact collection contract/mutation facts.
- Clone removal requires last-use, ownership, alias, effect, and destruction-order proof.
- Substring/view fixes require lifetime/escape proof.
- Representation/index/layout changes remain advisory unless public semantics and ABI are proven unchanged.

## Transform algorithms

Vector containment checks exact induction destination and `+1` constant first; until full dependence/alias/effect/target proof exists, the rewrite status is disabled and only analysis/remarks run.

CollectionPlan extracts producers, filters, mappings, reductions, materializations, cardinalities, callbacks, and ordering. Planner enumerates a bounded candidate set, proves legality, estimates resources, selects only positive plans, and records rejection reasons. Lowering uses true preheaders and preserves zero-trip behavior.

General fusion proves compatible lower/upper/step/order, dependence directions/distances, alias regions, effect/exception/destruction order, early exits, reduction numeric order, and profitability. Runtime alias versioning is Aggressive/profile-only and must preserve an unfused fallback.

Scalar passes rehabilitate in order: constant folding, copy propagation, DCE, local CSE, true LICM, reserve insertion, BCE, stack promotion, TCO, GVN; later string building, strength reduction, unrolling, fusion, and vector rewriting. Each activation is independent.

## Summary and profile formats

`PerfSummary` is fingerprinted by typed/MIR semantic hash, imported summaries, target layout, optimization config, and cost-model version. Bounded SCC propagation widens or returns incomplete. `.sperf` encodes deterministic static bounds/confidence/assumptions for CI diffs.

`.sprof-v2` is backward-compatible and adds optional typed records. Disabled instrumentation is compiled/branched out before allocations or I/O. Curve measurement uses >=4 sizes and repetitions, records distributions and startup subtraction, and never classifies from one timeout.

## Error handling

All analysis APIs use `AnalysisOutcome<T>`/`Result<T,E>`. Unknown and incomplete are data, not exceptions or optimistic defaults. Invalid pass/schema/config is an error before compilation. Verifier failure preserves pre-pass MIR, emits evidence, and stops. Cache mismatch discards/rebuilds once; repeated mismatch is explicit failure.

## Observability

Counters: parse/typed artifact builds/hits, fact builds/hits/rebuild reasons, nodes/edges/budget, pass candidates/transforms/rejections, instructions, elapsed, allocation/copy/COW bytes, summary invalidation, profile disabled/enabled activity. Stable IDs connect static and runtime evidence.

## Compatibility and rollout

Existing COLL behavior dual-runs during migration and must match ordered code/severity/span/fix/exit before ownership switches. Legacy JSON remains default until V2 admission. Pass rollback changes status to `Disabled(reason)` without deleting identity/schema. Existing `.sprof` v1 readers/writers remain supported.

## Verification mapping

REQ-001..005: pipeline/sentinel/verifier system and integration specs. REQ-006..009: revision reuse, exact spans, diagnostic compatibility. REQ-010..012: rule matrices and bounded costs. REQ-013..015: fact/invalidation/escape/COW adversarial tests. REQ-016..018: CollectionPlan/fusion/pass differential tests. REQ-019..023: summary/CI/profile/curve/hot-path measurements. REQ-024..025: facade guards, docs, traceability, and admitted pure-Simple provenance.

No UI design artifact is required: all surfaces are compiler CLI/LSP structured text/protocol outputs, covered by text/API/protocol evidence.
### Checked optimizer execution cost contract

Canonical module dispatch supports a fail-closed checked boundary. With
`SIMPLE_MIR_VERIFY_EACH` unset, the compiler reads that process setting once and retains
only an O(1) cached integer comparison per pass. It must not construct receipts, collect
or sort function identifiers, scan MIR, or allocate diagnostic strings on that path.

With verification enabled, or when `run_pass_on_module_checked` is called explicitly,
the boundary verifies the module before and after execution. Function-scoped passes sort
function identifiers for deterministic records and use the exact recorded function-pass
adapter. Its expected cost is O(F log F + B + I + A), where F is functions, B blocks, I
instructions, and A modeled operand/CFG accesses; transient memory is O(F + E), where E
is verifier evidence. This cost is accepted only for focused tests and opt-in compiler
diagnostics until incremental receipts exist.

SSA validation requests a verifier-specific `PerfFacts` projection. It retains CFG,
def-use buckets, reverse postorder, and immediate dominators, but omits dense liveness
USE/DEF/live-in/live-out matrices. Validation visits each definition and use bucket once.

Opcode checks reuse the structural instruction traversal and an O(locals) declared-type
dictionary. They compare `MirTypeKind` structurally rather than allocating serialized type
keys. Receipt coverage counters make partial admission machine-visible.

### Shared line-view quality checks

Traceability, SPipe-quality, and raw typed-UI rule owners receive the immutable line view
created by `lint_source`. These owners must not split `content` again or retain the view
beyond the request. Their cost remains one aggregate O(source lines) scan across the
rules, with no rule-local full-source arrays. Whole-text input is reserved for predicates
that cannot be expressed without cross-line context.

### Single-owner EasyFix dispatch

`lint_source` invokes the EasyFix registry exactly once and consumes only that returned
sequence. It must not invoke individual registry members again. This preserves registry
order, prevents duplicate diagnostics/replacements, and bounds each registered rule to
one execution per lint request. A future registry view API will share line/context facts
among its members without changing this ownership boundary.

### EasyFix source-view admission

The registry exposes `check_all_rules_with_lines(source, file, lines)` for compiler/lint
owners that already hold a canonical view. Spec-only context facts are constructed once,
only when the suffix admits SPipe rules, and passed immutably to each member. Standalone
rule and registry entrypoints remain compatibility boundaries and retain their early path
gates. Subsequent rule families should join this view incrementally; no process-global
source cache or unbounded retained context is permitted.

### General EasyFix fact sharing

The registry constructs exactly one general `LineContext` array from caller-owned lines.
Code, annotation, deprecation, module-boundary, and SPipe members consume that immutable
array or the canonical lines. Standalone wrappers construct equivalent private facts and
remain behavior-compatible. Duplicate-typed call-site discovery reuses canonical lines
for every signature, avoiding per-candidate arrays; its repeated traversal remains an
explicit candidate for a name-indexed call-site table. No view survives registry return.

### Compiler-owned split elimination

All compiler-owned EasyFix registry members that require line iteration accept canonical
lines or contexts. Path-gated compatibility wrappers must perform their gate before
splitting, so direct calls on excluded files remain allocation-free. File-scope allow
analysis has a lines variant and must not reconstruct the source view. Whole-source input
remains only for algorithms that inspect cross-line text without a migrated fact owner.

### Canonical EasyFix context ownership

`std.tooling.easy_fix.rules_helpers` is the sole owner of `LineContext` and
`EasyFixSourceView`. Compiler rule helpers re-export the type and builders; they must not
declare a parallel structural copy. The registry builds one view from canonical lines and
passes the same context array to compiler and stdlib rule owners. View-taking variants
preserve compatibility wrappers, rule order, byte offsets, and replacement ordering.
The view is request-scoped and must never enter a process-global cache.

### Indexed duplicate-typed call sites

Build a unique target dictionary keyed by function name and arity. Ambiguous targets are
excluded before source scanning. A single lexical line pass admits identifier tokens by
name, parses only candidate calls, and emits flat `(signature_index, sequence,
replacement)` records. Sort by signature and sequence to retain legacy grouping and
source order without nested mutable/COW replacement buckets. The bounded cost is
O(source + signatures + replacements log replacements), memory O(signatures +
replacements); future typed call resolution may replace the lexical index.

### Allocation-free lint metadata dispatch

Small immutable lint registries used on every diagnostic or annotation line are encoded
as exact match dispatch, not freshly constructed arrays. EasyFix ID decoding supports two
wire shapes: `L|E:code:location...` and `direct_code:location...`. It returns the semantic
code, preserves malformed input as an unknown authored code, allocates no parts array,
and never treats a location component as policy identity. Text and JSON severity paths
must consume this single decoded code.

### EasyFix policy reachability

Every EasyFix semantic code that has a declared configurable lint name must map exactly
to that name. Direct visibility warnings W0401–W0404 and W0406 map to the shared
`visibility_boundary` policy. Mapping uses exact match dispatch and precedes severity and
suppression projection; no diagnostic may bypass configured allow/warn/deny because its
producer uses EasyFix. Registry/default/mapping parity is a source-contract invariant.

Advisory EasyFix families use stable configuration owners even when several wire codes
represent one rewrite family. `short_grammar_method_ref`, `short_grammar_function_ref`,
`short_grammar_placeholder`, and `short_grammar_ignored_param` map to
`short_grammar_refactor`; contextual, deprecated, struct, raw-unit, and SIMD codes map
directly. All default to warning until an explicit profile decision changes them.

### Unknown-annotation fallback honesty

Raw-source EasyFix dispatch emits one generic `unknown_annotation` diagnostic because
`@name` alone does not prove decorator or attribute classification. Membership is the
union of both known sets. The generic policy is canonical; legacy `unknown_decorator` and
`unknown_attribute` settings alias it bidirectionally for compatibility. Only typed HIR
may emit category-specific findings. The fallback performs one context traversal and
allocates at most one fix per unknown line.

### Disabled transform body policy

A disabled transform exposes only its inert compatibility entrypoint, status/reason, and
analysis predicates that have independent consumers. Unreachable rewrite bodies after an
unconditional return are forbidden: they add parse/code memory and enable accidental
activation without proof gates. Collection hoisting remains identity until a replacement
accepts explicit preheader, dominance, memory-version, effect, zero-trip, and
speculatability evidence. Header insertion is never a substitute for hoisting.
## Fail-closed trip-count ownership

`LoopDetector` may identify natural-loop structure, but it must report `trip_count=nil` until the shared SCEV-lite owner proves the initial value, signed step, comparison direction and polarity, nowrap semantics, and finiteness. Disabled inference paths must not retain unreachable rewrite or recognizer bodies. Rehabilitation belongs in the shared fact service with positive, zero-trip, negative-step, overflow, and non-finite witnesses; it is not a one-line removal of a fail-closed return.
## TCO rehabilitation contract

The current TCO facade is a `Skeleton` identity and must contain no dormant rewrite body. A future active implementation must evaluate every recursive-call argument into fresh temporaries before assigning any parameter, then prove exact arity and MIR types, ownership and destruction timing, effect and unwind equivalence, entry-edge phi semantics, and debug-location preservation. Positive witnesses must include argument permutations and cycles; negative witnesses must cover non-tail calls, indirect recursion, throws/unwind, borrowed values, and observable destructors.

## CLI-scoped lint session

Repository lint should construct one `LintSession` per command. The session owns the immutable lint registry, parsed CLI policy, critical-mode policy, a directory-to-manifest cache, and a manifest-to-parsed-config cache. Per-file attributes are applied to a child configuration; cached configurations are never mutated. The CLI reads each source once and shares it with ordinary and SIMD checks. Session lifetime provides batch invalidation; long-lived daemon/LSP sessions must key cached policy by path plus content digest or validated metadata. This removes file-count-multiplied descriptor allocation, ancestor walks, configuration reads, and parsing without creating process-global stale state.
### Staged lint-session delivery

The first implementation stage reuses one command-owned `Linter` and a bounded last-project parsed-policy cache. It deliberately does not introduce a process-global cache. This immediately removes `O(files * rules)` descriptor construction and repeated adjacent manifest parsing while keeping configuration children isolated. The next stage adds bounded directory/manifest indexes and a source payload shared by lint, SIMD, and fix rendering; daemon/LSP caching remains digest-keyed and separate.
### Source payload ownership

Batch lint owns one immutable source payload per file. It passes the payload to ordinary lint and read-only sibling analyses such as SIMD opportunity detection. The reader returns a tagged success/error result so an unreadable file cannot be confused with valid empty source. Mutating fix application is intentionally outside this reuse contract: it must reread or otherwise validate a content digest immediately before atomic replacement.
### Critical policy snapshot

Command-scoped lint resolves `critical.dynamic_acquire` lazily once and retains the effective scalar mode rather than the complete configuration object. All files in one invocation observe one coherent policy snapshot. A subsequent command constructs a new session and reloads policy; long-lived daemon/LSP owners must use their separate digest-keyed invalidation contract.
### Bounded manifest discovery

The command session maps source directories and discovered manifest directories to the resolved `simple.sdn` path or an explicit miss. Each ancestor step consults the cache, allowing sibling trees to stop at a cached common ancestor. The cache retains at most 4096 directory entries; after the cap, discovery remains correct but uncached. A prepared source-path token prevents the downstream lint configuration layer from repeating discovery while still applying file-local attributes to a child configuration.
### Bounded parsed-policy storage

Manifest discovery and manifest parsing use separate caches. Parsed policies are stored in a flat array and addressed by a `path -> i64` index, avoiding class/struct-valued dictionary access. At most 256 unique policies are retained per command. Every hit returns a child configuration; CLI and file attributes never mutate the cached base. New paths after saturation follow the ordinary parse path without retention.
### Manifest-free policy base

The session owns one immutable moderate/default policy for files with no manifest. Per-file evaluation starts from `manifest_free_config.child()`: mutable override levels are copied/empty, while the effective-default dictionary is shared. Profile selection assigns a new defaults dictionary to the child and cannot alter the base. This removes rule-count-proportional default allocation per manifest-free file.
## Storage-layout advisory cost boundary

Advisory field deduplication uses indexed membership and an explicit count; it must not depend on `Dict.len()` or a growing array scan. Canonical identity rows use the standard deterministic text sort. The remaining pairwise overlap proof is semantically distinct: it rejects co-accessing different fields over intersecting logical ranges and stays quadratic until facts can be grouped by region and swept in stable interval order without losing fail-closed unknown-range behavior.
## String-builder rehabilitation contract

The current string-builder pass is a `Skeleton` identity and contains no dormant candidate or rewrite body. Rehabilitation must explicitly create a typed builder local, initialize it on the correct dominating path, preserve zero-trip results, append in observable order, emit a final join at every live exit, replace all dominated result uses, and prove ownership/destruction, allocation-failure, exception, alias, and debug semantics. Positive witnesses include zero/one/many iterations and multiple exits; incomplete push-only lowering is never admissible.

The current body-outlining pass is a `Skeleton` identity and contains no dormant cold-region extraction or synthetic-function rewrite. Rehabilitation requires profile or proved coldness, canonical region entry/exit structure, complete live-in and live-out SSA repair, ownership and destruction preservation, checked module symbol and ABI construction, unwind/exception and debug-location equivalence, and a profitability model covering code size, call overhead, and instruction-cache benefit. Direct class and module entrypoints must remain identities until positive, negative, and semantic differential witnesses satisfy that contract.
## Strength-reduction rehabilitation contract

Every callable strength-reduction surface—not only canonical dispatch—remains identity while status is `Disabled`. Rehabilitation must prove operand/result integer widths, signedness, non-negativity where required, overflow/trap semantics, shift legality, constant materialization, dominance and fresh-local allocation, and target profitability for each rewrite. Signed division/remainder and negative operands require dedicated differential witnesses. Provider metadata describes required facts but never authorizes a transform by itself.
## GVN rehabilitation contract

Every GVN callable surface remains identity while status is `Skeleton`. Rehabilitation requires dominator-tree traversal, dominance-scoped leader tables, structural interned expression keys, opcode type/trap semantics, and MemorySSA-lite versions for loads/calls/stores. Leaders are invalidated or scoped at control merges; block storage order is never evidence. Positive witnesses must include dominating reuse, while sibling branches, intervening writes/unknown calls, traps, and alias ambiguity are mandatory negative cases.

Local CSE follows the same fail-closed rule at basic-block scope. Its Skeleton contains no rewrite body or mutable leader selection. Rehabilitation must use structural keys without formatted text allocation; distinguish Copy from consuming Move; kill leaders on redefinition; model checked/trapping operations; and attach memory versions to loads, fields, stores, globals, intrinsics, indirect calls, and every unknown effect. An unchanged block must reuse its original storage rather than rebuilding arrays. Positive witnesses cover repeated pure expressions; negative witnesses cover moves, mutation, calls, traps, redefinitions, and unknown opcodes.

Scalar activation order is Copy-only local propagation, constant folding, local CSE, then DCE. Each step stays Skeleton until canonical dispatch, exhaustive opcode coverage, exact candidate/change/rejection receipts, positive and negative witnesses, semantic differential execution, and post-pass verification exist. DCE additionally requires an explicit sparse-versus-dense liveness budget so `O(blocks*locals)` storage and repeated local scans cannot become an unconditional compile-time tax.

Repository lint commands own an immutable `LintCliPolicy` parsed once after option normalization. Per-file execution receives only that policy, the path, the shared command `Linter`, and the already-read source; positional target arrays never enter the hot path. Project configuration is cloned from bounded caches, then the command profile is applied, then file-header policy is resolved. Compatibility entrypoints may parse args for a single standalone invocation but must not be used by repository loops. Policy parsing errors terminate before per-file analysis, and deprecated aliases are resolved once per command.

The current copy-propagation Skeleton contains no chain resolver or MIR rewrite helper. Its compatibility map stays empty and statistics stay zero. Rehabilitation is deliberately block-local and Copy-only first: build roots in one forward walk, reject cycles and redefinitions, rewrite every modeled operand/terminator family or fail the candidate as incomplete, and preserve original storage for unchanged blocks. Root resolution must use compression or another proven near-linear representation rather than a fixed-depth walk. Move participation is a separate ownership feature requiring consumption, lifetime, destructor, and borrow proofs.

Any reusable optimization engine separates cumulative session state from function-local analysis state. Optimization counts may accumulate across functions, but maps keyed by `LocalId`, block ID, expression leader, definition, use, alias, or memory version are recreated at the start of every function before all early returns. A future arena-backed implementation may clear and reuse capacity only when it proves no retained MIR/value graph survives and caps high-water memory; correctness never depends on numeric IDs being globally unique.

Constant evaluation and constant-fold optimization are separate owners. Semantic `const_eval` evaluates language-mandated constant contexts and stays in the semantics layer. Optional whole-program folding is admitted only through the typed MIR pass registry with status, witnesses, receipts, and verification. The HIR driver must not run a parallel best-effort optimizer or rebuild immutable HIR unless the resulting module is installed and equivalence is proved. Resolved HIR flows directly to validation/lowering today.

The lint combined-view handoff retains derived facts, not source-sized views. While the one canonical line array is live, text lint builds `LintSourceLocationIndex`; the command retains its three scalar dictionaries only until parsed append materializes the resolved config and index. It releases the handoff before AST rule loops. No `last_source_lines` field or local alias may extend split-text lifetime across parsing. Fallback callers may build the same index from content when no combined handoff exists.

MIR constant folding remains a zero-change Skeleton until the evaluator signature includes opcode, both typed operands, target configuration, and language overflow/FP mode, returning either a typed constant or a structured rejection. Integer evaluation uses exact width and signedness; division, remainder, shifts, overflow, and traps follow language rules. FP evaluation distinguishes F32/F64 and preserves rounding, NaN, infinities, and signed zero. Algebraic simplification must prove type and trap equivalence. Rewriters carry a changed flag and reuse original blocks/functions when unchanged; no direct method bypasses admission.

Lint diagnostic policy projection compacts the request-owned `Linter.results` array in place with separate read/write indexes. The invariant is `0 <= write <= read <= original_len`; scanning uses the captured original length, mutation writes only kept entries at or before the current read slot, and truncation occurs afterward. Ordering is stable. Severity adjustment creates a new diagnostic/result rather than mutating shared records. No local array alias or second filtered buffer is permitted because Simple arrays have value semantics across engines.
## Bounds-check elimination rehabilitation contract

Every BCE entrypoint remains identity while status is `Disabled`. A future transform must attach each range fact to exact SSA/value versions and a dominance region, prove lower and upper bounds, loop initialization/step/polarity/nowrap/finiteness, zero-trip behavior, array-length stability, alias/mutation invalidation, and exceptional control flow. Proofs are structural facts, not global text keys; failure or timeout preserves the check. Direct block APIs can expose analysis remarks but cannot bypass canonical transform admission.
## General loop-transform rehabilitation contract

LICM, full/partial unrolling, and combined loop optimization remain identity at every callable surface while disabled. LICM requires canonical preheaders, dominance/post-dominance, MemorySSA-lite, alias/effect invalidation, speculatability/trap and zero-trip proof. Unrolling additionally requires exact induction/trip semantics, SSA renaming, exit/continue/break/unwind preservation, ownership/destruction order, code-size/register-pressure profitability, and target validation. Combined passes route only through status-aware dispatch; they never chain class methods around it.
## Generator analysis and rehabilitation contract

`analyze_yields` is an analysis-only storage-order scaffold. It may report conservative named/argument locals but does not prove CFG liveness or frame layout. Generator transformation remains identity until shared def-use/liveness, suspension ownership, frame type/layout/alignment, state ABI, exception/unwind, drop/destruction, reentrancy, debug, and runtime protocol contracts are complete. Rehabilitation uses a dedicated lowering owner and positive runtime witnesses; optimizer class methods never independently invent the coroutine ABI.

## Dead-code-elimination rehabilitation contract

DCE is a zero-change Skeleton at every callable transform surface. Compatibility
observability queries fail closed and probe classification cannot authorize
deletion. Activation requires exhaustive opcode def/use and observability facts,
including traps, ownership/destruction, unwind, volatile/atomic/device behavior
and debug probes. Liveness must use sparse/worklist storage with bounded CPU and
memory, expose incompleteness, reuse unchanged MIR storage, and pass activation,
differential, idempotence and IR-verification gates.

## PerfFacts capability and allocation contract

Consumers explicitly select whether liveness is required. The no-liveness
builder produces CFG, reverse-postorder, dominance and def-use while leaving
DEF/USE matrices, live-in/live-out matrices, visits and exhaustion state empty.
The ambiguous full builder retains compatibility but must not be used by active
analyses that do not query liveness. `PerfFactRequest` validates dependencies
among CFG, dominance, def-use and liveness and constructs only the dependency-
closed capabilities. Raw missing dependencies remain reportable even though the
runtime builder closes them safely. Unrequested families have empty storage and
`complete = false`; queries therefore fail closed.

Dominance availability is explicit through `dominators_complete`; an empty map
never means success. Any consumer that interprets def-use sites by block ID or
rewrites MIR requests CFG+def-use and checks both completeness bits. Def-use-only
is reserved for analyses whose result remains conservative without CFG identity.

## Diagnostic rendering allocation contract

Warning/error formatters accumulate complete logical records and join once.
Evidence cardinality must produce linear payload construction; per-evidence
immutable append is prohibited. Human and JSON rendering preserve source order,
escape each JSON item once, and keep exact output compatibility.

## Accessor rewrite indexing contract

The compiler rule registry supplies one canonical `[text]` plus `LineContext`
view to accessor-field analysis. The analyzer parses class/method facts from
those lines, builds per-class real-field and accessor-name indexes, and scans
each class line only for accessor-shaped call occurrences. Exact-name conflicts
are ambiguous and suppress rewriting. Replacement offsets come from the shared
contexts; active registry paths never split source or build parallel start
arrays. Compatibility source APIs may construct one local view.

## Warning candidate and cursor contract

Backward annotation/suppression scans run only after a rule has recognized a
candidate declaration. Every rejected line advances its byte offset exactly
once. Repeated token/delimiter searches use absolute forward cursors over the
original text; they never allocate a suffix per match. Each warning entrypoint
has one method owner so diagnostic construction and policy cannot diverge across
duplicate declarations.

## Lint deduplication collection contract

Rules that need membership only use dictionary/set storage plus an explicit
count when native dictionary length is not an admitted contract. They do not
scan a growing array for every candidate. Ordering-sensitive diagnostics retain
an ordered result array separately; count-only rules such as `wide_public` never
iterate the membership dictionary.

## Diagnostic override fast-path contract

Serialized diagnostic code extraction is conditional on a positive explicit
override-entry count. The lint-config loader is the sole owner of the override
dictionary/count pair: clear resets both, and every insertion increments the
count exactly once. Default-policy emission must not scan JSON or allocate a code
substring. The count is authoritative because dictionary length is not an
admitted cross-engine contract.

## CFG predecessor bucket contract

PerfFacts constructs predecessor adjacency in two phases. Edge discovery maps a
successor block ID to one owned bucket and appends the source ID exactly once per
terminator edge. Publication assigns each completed bucket to the public
dictionary once. Bucket-key order is internal; predecessor-list order follows
function block storage and terminator successor order. Duplicate edges and
dangling targets are retained so CFG integrity diagnostics remain behaviorally
identical. Builder indexes and outer bucket storage are released immediately
after publication. No edge loop may read, grow, and write back a
dictionary-held array.

## Short-lambda candidate scan contract

Short-grammar discovery performs one forward line scan. The first `#` terminates
discovery exactly as in the compatibility scanner; each quote toggles the existing
single-line string state; only an unquoted backslash followed by an identifier
start or `(` becomes a candidate. Parsing may advance a consumed offset, and
precomputed candidates before that offset are skipped. Discovery must not recurse
or rescan a growing prefix per backslash. Candidate position storage is linear in
eligible candidates and is released after the line. Functional-update exclusion
computes the first non-function-type arrow once only when the line has an eligible
lambda candidate; candidate filtering compares only its numeric position and
never rescans the line prefix.

## Incomplete liveness storage contract

Dense liveness arrays exist only when their fact family is requested, the cell
budget is admitted, and prerequisite CFG/def-use facts are complete. The builder
checks completeness before allocating live-in/live-out. If completeness becomes
false after USE/DEF collection, the request returns empty USE, DEF, live-in, and
live-out arrays with `liveness_complete = false`. Consumers must gate on that bit;
incomplete matrices are never retained as shape-compatible placeholder data.

## CLI policy projection identity contract

`lint_run_result_apply_cli_policy` computes effective severity once. When it
equals the diagnostic's current level, the immutable `LintRunResult` is returned
directly; no result or diagnostic payload is reconstructed. When severity changes,
one new diagnostic/result is created. Callers must not mutate either path, and
rendered output, counts, ordering, fix identity, evidence, and uncertainty remain
identical.

## Natural-loop latch bucket contract

Loop detection maps each dominance-proven header to one owned latch-array index
and one membership set. First header discovery fixes loop-output order. First
source/header discovery fixes backedge order; duplicate terminator edges from the
same source to the same header are ignored. The edge loop performs no growing
array extraction, linear duplicate scan, or dictionary copyback. Incomplete CFG
or dominance still produces no loops, and loop body/exit construction is
unchanged.
