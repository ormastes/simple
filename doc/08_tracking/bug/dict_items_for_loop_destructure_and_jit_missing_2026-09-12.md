# `for k, v in d.items()` fails in the interpreter; `Dict.items` is missing under JIT

- Status: PARTIALLY FIXED (2026-09-12) — both original defects fixed and
  verified in-tree (worktree `simple-dict-items`, branch
  `work/dict-items-for-loop`); **the lead-mandated static-rule design leaves
  two checked-in `test/04_smoke/` tests at their deployed-seed RED state —
  see "Design conflict, needs a lead decision" below, first.** Not
  landed/committed by this pass, see Verification below.
- Found: 2026-09-12
- Component: seed interpreter for-loop pattern binding (Rust parser
  `parse_for_pattern` + the static disambiguation in
  `interpreter_helpers/patterns.rs`); JIT/MIR lowering builtin method table
  (`Dict.items`, `mir/lower/lowering_expr_method.rs`); JIT erased-receiver
  builtin dispatch (`codegen/instr/closures_structs.rs`, for parity with
  `keys`/`values` on an untyped receiver)
- Lane: interpreter (defect 1), JIT/native (defect 2)

## Reproduction

```simple
fn main():
    var d: {text: i64} = {"a": 1, "b": 2}
    var acc = 0
    for k, v in d.items():
        acc = acc + v
    print("{acc}")
```

| form | `SIMPLE_EXECUTION_MODE=interpreter` | default (JIT) |
|---|---|---|
| `for k, v in d.items():` (the form documented in `doc/07_guide/quick_reference/syntax_quick_reference.md` ~L885) | `error: semantic: type mismatch: cannot convert tuple to int` | `Runtime error: Function 'Dict.items' not found` |
| `for (k, v) in d.items():` | `3` (correct) | `Runtime error: Function 'Dict.items' not found` |
| `for kv in d.items(): acc = acc + kv.1` | `3` (correct) | `Runtime error: Function 'Dict.items' not found` |

Deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-06 09:59.

## Defects

1. Interpreter: the unparenthesised two-name for-pattern over `items()` binds
   the whole tuple to the first name and the second name to nothing usable
   (`v` is the tuple), i.e. `for k, v in …` is not desugared to the
   parenthesised tuple pattern that works. The quick reference documents the
   unparenthesised form.
2. JIT/native: `Dict.items` has no builtin binding at all, so every `items()`
   loop only runs in the interpreter lane.

## Fix direction

1. Normalise `for a, b in e` to `for (a, b) in e` at parse or lowering time
   (one site), pinned by a spec that runs both spellings and compares.
2. Add `items` beside `keys`/`values` in the JIT builtin dispatch and the
   native runtime, pinned by a lane-parity spec.

## Design conflict, needs a lead decision (read this first)

This is a CROSS-ENGINE semantics conflict, not two seed-interpreter tests
disagreeing with each other. `test/04_smoke/compiler_unparenthesized_tuple_for.spl`
reads as a regression test for the PURE-SIMPLE compiler's for-loop semantics
— its own header says "the core-c bootstrap lane deliberately does not
provide the dynamic `Array.enumerate` method symbol" — and the pure-Simple
parser (`src/compiler/10.frontend/core/parser_stmts.spl`,
`encode_for_tuple_binding`) has NO enumerate-shorthand concept at all: a bare
comma list is UNCONDITIONALLY a tuple pattern, always, regardless of what the
iterable is. Under that model `for a, b in rows:` and `for (a, b) in rows:`
are identical by construction, which is exactly what the smoke test asserts.
The Rust SEED interpreter is different: it has a genuine, separately-tested
enumerate-shorthand FEATURE (`for i, item in items:`) that pure-Simple simply
does not have. This smoke test was RED on the deployed seed at the start of
this bug (measured, not assumed) — it never passed on the seed until this
session's first fix attempt (Design 1 below) made it pass, incidentally, as
a side effect of a different, broader (and ultimately rejected) mechanism.
The task brief for this bug said to check the pure-Simple parser and "keep
them consistent"; the lead's Design 2 instruction (below) makes them
**explicitly, deliberately inconsistent** for this one shape: `for a, b in
<bare array of pairs>:` destructures under pure-Simple, enumerates under the
seed. That inconsistency — real before this session touched anything, just
never previously exercised by a passing-then-regressed test — is the thing
that needs a lead decision, not a mistake in either fix attempt.

Two designs were tried in this session; neither reconciles the two engines'
models. **This fix ships the SECOND design, per an explicit follow-up
instruction naming the first one's flaw** — which leaves
`test/04_smoke/compiler_unparenthesized_tuple_for(.runtime).spl` at their
ORIGINAL deployed-seed RED state under the interpreter (not a NEW failure;
they simply never left that state except during this session's rejected
first attempt). Nothing further was reverted or auto-resolved; this needs a
decision from whoever owns both the bug and the smoke tests — most likely
either relaxing/rewriting the smoke tests to match the seed's real,
documented enumerate feature, or accepting Design 1's data-dependent
enumerate flaw instead.

**Design 1 (per-item, at runtime):** decide, for each yielded value
individually, whether to enumerate-wrap it or destructure it, based on
whether that VALUE is already a 2-tuple. This made `d.items()`/`d.entries()`
correct and, as a side effect, made
`test/04_smoke/compiler_unparenthesized_tuple_for(.runtime).spl` — a
pre-existing, already-checked-in regression test asserting `for index, name
in rows:` (`rows` an array of 2-tuples) destructures exactly like `for
(index, name) in rows:` — pass under the interpreter for the first time (it
was RED on the original deployed seed; its JIT side was already GREEN via a
different code path). Its own header comment: "unparenthesized tuple
bindings must encode exactly like the adjacent parenthesized form." **Flaw:**
it silently reinterprets `for i, pair in [(1, 2), (3, 4)]:` — ordinary
enumerate over an array that happens to hold 2-tuples — as destructure,
because the per-item check cannot distinguish "this array is pairs I want to
enumerate" from "this array is (key, value) pairs I want to unpack." Whether
`i` becomes 0/1 or 1/3 depends on the CONTENTS of the array at runtime, not
the source text — a real, data-dependent feature break.

**Design 2 (static, on the iterable expression — what ships here):** destructure
only when the for-loop's iterable is syntactically a `.items()`/`.entries()`
method call (any receiver); every other iterable — including an array
literal/variable of 2-tuples — keeps the plain enumerate shorthand exactly as
before this bug existed. This fixes `d.items()`/`d.entries()` (both are
always written as that method call) and correctly keeps `for i, pair in
[(1, 2), (3, 4)]:` as enumerate. **Flaw:** `rows` in the smoke tests above is
a bare identifier holding an array of 2-tuples, not a `.items()`/`.entries()`
call — under this design it is indistinguishable from `[(1, 2), (3, 4)]` and
therefore ALSO enumerates, not destructures. Measured on the final binary:
`test/04_smoke/compiler_unparenthesized_tuple_for.spl` under
`SIMPLE_EXECUTION_MODE=interpreter` prints
`tuple-for-fail=0:(0, aether);1:(1, glass); adjacent=0:aether;1:glass;` —
byte-identical to the ORIGINAL unfixed deployed seed's output, i.e. this
specific smoke test is back to exactly its pre-this-bug RED state. Its JIT
side is unaffected (still `tuple-for-ok=...`) since JIT never went through
either version of this interpreter-side logic.

No design tried satisfies both tests, because the two tests assert opposite
semantics for the identical shape (`for a, b in <bare-array-of-tuples>:`).
Resolving this for real needs either: relaxing/rewriting the smoke tests to
match Design 2's contract (bare arrays of tuples enumerate; only
`.items()`/`.entries()` destructure), reverting to Design 1 and accepting its
data-dependent-enumerate flaw, or a THIRD design not yet explored (e.g. a
type-level marker distinguishing "array of pairs" from "dict view", which
would need type information this interpreter code path does not have).
**Not decided by this pass** — the smoke tests were left as-is (not modified,
per "never skip a failing test without approval"), and their current RED
state under Design 2 is reported below rather than hidden.

## Fix applied (2026-09-12) — Design 2, per the instruction above

**Defect 1** — `parse_for_pattern`
(`src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`) is unchanged
from before this bug's fix: a bare two-name pattern still parses to
`Pattern::Tuple([Identifier(a), Identifier(b)])` with `auto_enumerate = true`
(parenthesized patterns and three-or-more bare names are unaffected, always
`auto_enumerate = false` — no grammar change, no `doc/06_spec` regeneration
needed). What changed is how the interpreter resolves that ambiguity: a new
static predicate,
`for_loop_iterable_is_items_or_entries_call`
(`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`), inspects
the for-loop's iterable `Expr` ONCE PER LOOP — `true` iff it is an
`Expr::MethodCall { method, .. }` named `"items"` or `"entries"` (any
receiver, any arity as written). Direct dict iteration (`for k, v in d:`,
`Value::Dict` at runtime, no method call at all — no syntactic marker exists
for this shape) keeps the SAME runtime-value check
(`matches!(iterable_value, Value::Dict(_))`) this file already had before
this bug's fix; NOT widened to `Value::FrozenDict` (`for k, v in frozen:`
still double-wraps — a real, separate, pre-existing gap, left alone rather
than folded into this fix, since the lead's instruction was "every other
iterable keeps today's shorthand exactly"). The combined boolean
(`items()`/`entries()` call OR runtime `Value::Dict`) is computed once per
loop and gates the existing wrap-vs-bind-directly branch at all three
duplicated for-loop execution sites: `interpreter_control.rs`
(`exec_for_inner`) and both copies in `interpreter_call/block_execution.rs`
(the closure/block-body executor used by `it` blocks). This replaces a
rejected earlier per-item runtime version of this same fix (Design 1 above,
`for_loop_enumerate_bind_value`, deleted) that decided per yielded VALUE
rather than per iterable EXPRESSION.

Known, deliberately-unfixed pre-existing gaps under Design 2 (same class as
this bug, same double-wrap symptom, all confirmed byte-identical between the
original deployed seed and every rebuild in this session — i.e. NOT
introduced or affected by this fix in either direction):
- `for k, v in frozen:` (direct `FrozenDict` iteration, no `.items()`).
- `for i, x in arr.enumerate():` — `.enumerate()` is a third alias the static
  rule does not recognise. Confirmed still double-wrapped UNDER SEED
  INTERPRETER SEMANTICS (`0:(0, a);1:(1, b);2:(2, c);` instead of
  `0:a;1:b;2:c;`) on both the original deployed seed and the final binary
  here. Live call sites matching this exact shape exist at
  `src/compiler/30.types/variance_types.spl:261` and `:476`
  (`for i, param_name in param_names.enumerate():` /
  `for i, arg in args.enumerate():`) — but that file is under
  `src/compiler/`, i.e. COMPILER source built/interpreted by the PURE-SIMPLE
  toolchain during bootstrap, where bare comma is unconditionally a tuple
  pattern and this shape is CORRECT (no enumerate-shorthand feature exists
  there at all — same pure-Simple-vs-seed distinction as the Design conflict
  section above). Whether the Rust SEED interpreter (where this double-wrap
  bug actually lives) ever executes `variance_types.spl` was NOT checked in
  this pass — the claim here is scoped to "this shape double-wraps under
  seed-interpreter semantics," not "this file is broken in production."
  Predates this session and this bug entirely either way; flagging it as a
  newly-noticed, separate, out-of-scope, and unverified-severity defect
  rather than silently walking past it — worth its own bug record and a
  proper engine-reachability check before any fix.
- `for i, pair in <bare identifier holding an array of 2-tuples>:` — see the
  Design conflict section above; this is the smoke-test regression, not a
  new gap, but listed here for completeness of what Design 2 does NOT
  destructure.

**Defect 2** was narrower than first suspected for the bug's own (statically
typed) repro: `Dict.entries()` already resolved correctly under the JIT (MIR
lowering, `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:757`,
already declared `rt_dict_entries` — see that function's own pre-existing
comment) — only the `if method == "entries"` guard failed to also accept the
`"items"` alias that the HIR type-inference table
(`hir/lower/expr/mod.rs:1734`, `"items" | "entries" => Some(TypeId::ANY)`)
already treated as equivalent. Changed the guard to
`matches!(method, "entries" | "items")`.

Separately, per the literal task wording ("add `items` beside `keys`/`values`
in the JIT builtin dispatch"): an ERASED (untyped-parameter) receiver's
`.items()`/`.entries()` was a second, PRE-EXISTING gap distinct from the bug's
own typed repro — `keys`/`values` already worked on an erased receiver (via
`codegen/instr/closures_structs.rs`'s bare-builtin-collection gate,
`is_bare_builtin_collection_method` ~L113, and its dispatch table ~L2318,
both keyed on method name alone for a receiver with no static type) but
`entries`/`items` did not (`Runtime error: Function 'entries'/'items' not
found`, confirmed for BOTH aliases symmetrically before this addition).

Added `("items", 0)` to the gate and `"items" => "rt_dict_entries"` to the
dispatch table — **deliberately `items` only, not `entries`**, even though
both alias the identical runtime call. A first attempt added both together;
a census before rebuilding —
`grep -rnE '^\s*(pub\s+)?fn (items|entries)\s*\(\s*(self\s*)?\)' src/lib
src/app src/compiler test` — found ZERO user-defined `items()` methods
anywhere in the tree, but NINE user-defined `entries()` methods on other
types (`Map`/`nogc_sync_mut/src/map.spl`,
`HashMap`/`nogc_sync_mut/src/collections/hashmap.spl`,
`PersistentMap`/`PersistentSortedMap`/`PersistentTrie`
(`nogc_async_immut/persistent_*`), `ConcurrentCollections`
(`nogc_async_mut/concurrent/collections.spl`, x2),
`FileStateCache`/`llm_caret`, `PersistentDict`/`interpreter/collections`).
`is_bare_builtin_collection_method` is exactly the erased-receiver-THEFT gate
this file's own history is full of (`RingWindow.push`, `SuffixRegistry.has`,
`ListIter.len`, `StaticCompressionCache.get` — all real, previously-shipped
miscalls this same file documents fixing): routing a bare `.entries()` there
risks silently stealing a call meant for one of those nine types' own
`entries()` and returning nil instead (`rt_dict_entries`/`dict_collect`
tag-checks the receiver and no-ops to nil on a non-Dict, per
`runtime/src/value/dict.rs:310`, rather than crashing — which makes the
wrong answer silent, not loud). `items()` carries none of that risk, so only
it was added; `entries()` on an erased receiver keeps its pre-existing
"Function 'entries' not found" behavior unchanged (verified: still raises
that exact error after this fix, same as before). `keys`/`values` carry the
identical theft risk against the same nine types' own `keys()`/`values()`
methods and have apparently carried it since before this bug — an existing
condition this fix neither introduces nor extends, called out here rather
than silently inherited. Guarded against regression by two new Rust
assertions in `erased_dict_views_use_builtin_dispatch`
(`codegen/instr/closures_structs.rs`): `items` IS in the gate, `entries` is
NOT. `rt_dict_entries` already exists in both the Rust runtime
(`runtime/src/value/dict.rs:349`) and the C runtime
(`src/runtime/runtime_native.c:9470`), so this needed no new runtime symbol.

## Verification

Binary identity of the FINAL rebuilt candidate used for all GREEN/RED evidence
below: `src/compiler_rust/target/release/simple`, built via
`cd src/compiler_rust && cargo build --release --bin simple`, size
51182552 bytes, mtime 2026-09-12 11:03 KST (worktree `bin/simple` repointed to
it — a symlink change local to this worktree, not an edit to the shared main
worktree). RED evidence for the spec was captured against the unmodified
deployed seed, `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(size 50093192, mtime 2026-09-06 09:59), before any source edit was built.
This is the SECOND fix design in this session (see "Design conflict" above);
Design 1 was built and verified first, then replaced.

- New regression spec `test/01_unit/language/dict_items_for_loop_spec.spl`
  (+ required companion probe
  `test/01_unit/language/probe_dict_items_for_loop.spl`, executed as a
  subprocess under both engines — same pattern as the existing
  `engine_divergence_mutation_class_spec.spl` /
  `probe_engine_divergence_mutation_class.spl` pair in the same directory;
  not a scratch file, the spec cannot run without it). RED on the deployed
  seed: `3 examples, 3 failures` (interpreter describe) / `2 examples, 2
  failures` (JIT describe) — the probe crashes before printing anything, so
  every field reads `"MISSING"`. GREEN on the final binary: `3 examples, 0
  failures` / `2 examples, 0 failures`. Covers:
  - defect 1 core repro: bare vs. parenthesized `d.items()` for-loops agree
    and match an independently-computed literal oracle (`EXPECTED_TOTAL=6`
    for `d = {"a":1,"b":2,"c":3}`), both lanes;
  - **pin (a)** (regression guard, interpreter only — see "Design conflict"
    for why JIT is excluded): `for i, pair in [(1, 2), (3, 4)]:` still
    enumerates, `IDX_SUM=1`, `PAIR_REPR=1-2;3-4;`;
  - **pin (b)**: `for k, v in d.entries():` destructures the same as
    `.items()`, `ENTRIES_BARE_TOTAL=6`, both lanes.
- Direct repro from this doc, both engines, final binary:
  `EXPECTED_TOTAL=6 UNPAREN_TOTAL=6 PAREN_TOTAL=6 KV_MATCH=1 COUNT_MATCH=1
  ENTRIES_BARE_TOTAL=6` under both `SIMPLE_EXECUTION_MODE=interpreter` and
  `SIMPLE_EXECUTION_MODE=jit`; pin (a) fields `IDX_SUM=1 PAIR_REPR=1-2;3-4;`
  under the interpreter, `IDX_SUM=4 PAIR_REPR=nil-nil;nil-nil;` under the JIT
  (the pre-existing, unrelated JIT gap — see below — byte-identical to the
  original deployed seed).
- Erased (untyped-parameter) receiver, final binary, JIT: `d.items()`
  resolves and sums correctly (`ERASED_SUM=6`; raised `Runtime error:
  Function 'items' not found` before the `closures_structs.rs` addition).
  `d.entries()` on the same erased receiver deliberately still raises
  `Runtime error: Function 'entries' not found` — unchanged, by design, per
  the theft-risk census above.
- Direct dict iteration (`for k, v in d:`, no `.items()`), final binary: top
  level under both `SIMPLE_EXECUTION_MODE=interpreter` and JIT
  (`TOP_LEVEL=6`), and inside a spec `it` block (the
  `interpreter_call/block_execution.rs` path, `1 example, 0 failures`) — all
  three for-loop execution sites verified directly, not just inferred from
  source reading.
- Regression check for the plain-value enumerate idiom:
  `for i, item in ["a","b","c"]:` under `SIMPLE_EXECUTION_MODE=interpreter`
  still prints `0:a;1:b;2:c;` (unchanged) on the final binary.
  (Pre-existing, unrelated JIT divergence noted for the record: the same
  source under the JIT prints `a:;b:;c:;` on both the deployed seed and the
  final binary — the JIT's bare-enumerate loop over ANY plain array,
  tuples or not, has never implemented "enumerate" correctly; this is the
  same defect class as pin (a)'s JIT gap above, confirmed byte-identical
  before and after every rebuild in this session, out of scope for this bug.)
- `test/01_unit/app/interpreter/perf_spec.spl` ("enumerated integer/float
  array foreach index sum preserves accumulator") — the fast-path pin — still
  green: `41 examples, 0 failures`.
- `test/04_smoke/compiler_unparenthesized_tuple_for.spl` and
  `..._runtime.spl`: **RED under `SIMPLE_EXECUTION_MODE=interpreter`** on the
  final binary — `tuple-for-fail=0:(0, aether);1:(1, glass);
  adjacent=0:aether;1:glass;` — byte-identical to the ORIGINAL deployed
  seed's failure (this is the Design 2 regression, not a new failure mode;
  see "Design conflict" above). GREEN under JIT (`tuple-for-ok=...`),
  unaffected either way. **Do not read this as green-across-the-board without
  reading the Design conflict section first.**
- Neighbor specs unaffected: `dict_get_option_match_spec.spl` (2 examples, 0
  failures), `for_loop_var_shadows_prior_local_binding_spec.spl` (1 example,
  0 failures). `engine_divergence_mutation_class_spec.spl` (2 examples, 2
  failures), `compiler/mir/dict_typed_method_lowering_source_spec.spl` (3
  examples, 3 failures), and `compiler/mir/erased_dict_views_source_spec.spl`
  (a source-content assertion checking `mir/lower/lowering_expr_method.rs`
  for a literal string, `... (method == "values" or method == "keys") ...`,
  that no longer exists anywhere in the file — `receiver_is_dict`/
  `resolution_is_unresolved` predate a refactor; grepped the current source
  to confirm) fail identically on both the deployed seed and the final
  binary — pre-existing, unrelated to this change.
- `cargo test --release -p simple-parser --lib -- for`: 35 passed, 0 failed.
- `cargo test --release -p simple-compiler --lib patterns::`: 24 passed, 0
  failed (includes the `cow_alias_mechanism_tests` value-semantics pins).
- `cargo test --release -p simple-compiler --lib lowering_expr_method::`: 3
  passed, 0 failed.
- `cargo test --release -p simple-compiler --lib closures_structs::`: 6
  passed, 0 failed, including `erased_dict_views_use_builtin_dispatch`
  extended with the new `items`-yes/`entries`-no assertions (the regression
  guard for the theft-risk decision above).
- `sh scripts/check/check-rt-dual-implementation-ratchet.shs`: `PASS — 2517
  symbol(s) checked against 2517 baselined, 0 new, 0 stale` (no `rt_*` symbol
  touched by this change).
- `sh scripts/check/check-c-runtime-compiles-push.shs --rev HEAD`: `PASS —
  144 file(s) compiled, 0 errors (5 skipped for unavailable external
  dependencies)` — checks committed content only, which excludes this
  pass's uncommitted edits; unaffected regardless since no `.c` file was
  touched.

Not committed by this pass — worktree left dirty for lead review per lane
policy.

## Related

- `tuple_destructuring_does_not_bind_2026-07-27.md` (earlier tuple-binding gap)
- Newly noticed, separate, unfixed: `for i, x in arr.enumerate():`
  double-wraps under seed-interpreter semantics, both under this fix and the
  original code, with matching-shape call sites at
  `src/compiler/30.types/variance_types.spl:261,476` (compiler source, pure-Simple
  semantics — reachability under the seed interpreter unverified) — see
  "Fix applied" above. Worth its own bug record.
