# Bug: interpreter array mutating methods (`push`/`pop`/`insert`/...) clone the whole array every call — O(N²) list-building

- **Date:** 2026-07-08
- **Severity:** high (silent perf cliff, pervasive pattern — idiomatic `arr.push(x)` list-building)
- **Area:** Rust seed interpreter (`bin/simple` running `SIMPLE_EXECUTION_MODE=interpret`) —
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`,
  `src/compiler_rust/compiler/src/interpreter_method/collections.rs`,
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs`. Contrast:
  `src/compiler_rust/compiler/src/interpreter/node_exec.rs` (index-store, already fast).
- **Status:** status: RESOLVED (triage-confirmed 2026-07-17: Track A implemented + verified 2026-07-07, O(N²)→O(N) confirmed)
  Fix plan: `doc/03_plan/compiler/perf/interp_array_mutating_method_fast_path_plan.md`.
- **Source sweep:** this record is the corrected write-up of Task #33's completed sweep,
  `/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/bare_array_param_sweep.md`
  (full characterization table, repro files, mechanism). Independently cross-checked against
  current source for this record (line citations below refined past what the sweep guessed —
  see "Mechanism" for the delta).

## IMPORTANT — supersedes an earlier, unlanded, refuted draft

An earlier draft bug record, `compute_styles_nodes_arg_copy_quadratic_2026-07-07.md`, attributed a
residual `compute_styles` quadratic to **bare-array-parameter COPY** ("passing `nodes: [Node]`
deep-copies per call") with fabricated ~230–965 µs/call numbers. **That draft never landed** — it
was caught and refuted by adversarial review (two independent agents) before commit and does not
exist anywhere in the repo or history. It is recorded here only so the false narrative does not
resurface. The actual finding, confirmed by the sweep and re-verified below, is the opposite of
that draft's premise:

- **Passing a bare array parameter (any `[T]`, incl. `[HNode]`/class instances, any call depth,
  read usage) is O(1).** Arrays bind by `Arc` on call; reading through the parameter never clones.
  Measured flat from N=1e3 to N=1e6 (sweep table A) — a true per-call deep copy at N=1e6 would be
  ~1000× slower than at N=1e3 (~15 s); observed is ~53 ms, ~1000× *faster* than that hypothesis
  predicts, i.e. no copy.
- **The real O(N²) landmine is array-mutating methods, not parameter passing.** `compute_styles`'s
  own residual superlinearity is unrelated to this bug too — it was correctly re-attributed to
  `text.substring()`'s O(offset) cost in
  `doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md`.

## Symptom

`arr.push(x)` (also `append`/`insert`/`pop`/`remove`/`extend`/`clear`) in a loop is **O(N²)**
under the interpreter: every single mutating-method call clones the entire backing array, not
just the mutation. This is the idiomatic way to build a list in Simple, so the cost is pervasive
across the codebase, not confined to one hot path. The functional-reassignment spelling
(`x = x.push(...)`) is exactly as bad — the copy is inside the method, reassignment doesn't avoid
it.

By contrast, `arr[i] = value` (index-store) into a uniquely-owned local array is O(1)/op — this
was already fixed at some point in the past (see Mechanism) and is the "positive control" that
proves the harness detects real copies when they occur.

## Measured evidence (from the sweep; `SIMPLE_EXECUTION_MODE=interpret`, deployed self-hosted `bin/simple`)

**Fill N elements: `a[i] =` into a preallocated local vs. `a.push()` growing a local**, µs total:

| N | `a[i]=` (prealloc) | `a.push()` (grow) | push/idx ratio |
|---|---|---|---|
| 2000  | 1,511  | 19,081    | 12.6× |
| 4000  | 2,921 (1.9×/dbl) | 68,761 (3.6×/dbl)   | 23.5× |
| 8000  | 6,105 (2.1×/dbl) | 261,422 (3.8×/dbl)  | 42.8× |
| 16000 | 12,029 (2.0×/dbl) | 1,010,522 (3.9×/dbl) | **84×** |

`a[i]=` scales ~2×/doubling (clean O(N) total, O(1)/op). `a.push()` scales ~3.6–3.9×/doubling
(clean O(N²) total) and is diverging — 84× slower than the index-assign equivalent at N=16000.
Same shape confirmed for `[i64]`, `[text]`, and `[Node]` (class-instance) element types — element
type changes only the constant, never the complexity class.

**For comparison, bare array parameter pass + read (the refuted premise) is flat O(1)** across
1000× the N range (K=2000 calls each):

| N | read `[i64]` a[0] | read `[Node]` a[0].v | 2-level pass-down |
|---|---|---|---|
| 1e3 | 14,924 | 27,057 | 19,204 |
| 1e4 | 21,540 | 26,173 | 21,489 |
| 1e5 | 15,772 | 19,510 | 10,625 |
| 1e6 | 52,865 | 47,380 | 30,373 |

(The ~2–3× uptick at 1e6 is allocator/cache noise, not a copy — a real per-call deep copy would
show ~1000× growth, i.e. ~15 s, not 53 ms.)

Also: mutating an **aliased** array (`mut` param while caller retains a reference, module global,
captured closure var — `Arc` strong_count > 1) costs O(N)/op regardless of whether the mutation is
`push` or `a[i]=` — aliasing, not the specific method, is what forces the clone in that case. It is
the **unaliased, locally-owned** case where `push` is pathological and `a[i]=` is not, because only
`a[i]=` has an in-place fast path for that case (see Mechanism).

## Mechanism (source-confirmed; more precise than the sweep's initial guess)

Value arrays in the running interpreter (the Rust seed, `Value::Array(Arc<Vec<Value>>)`) are
`Arc`-shared on bind/pass. Two code paths handle "identifier holds an array, do something to it,"
and only one of them has an ownership fast path:

**Index-store `a[i] = x` — HAS the fast path**
(`src/compiler_rust/compiler/src/interpreter/node_exec.rs:906-937`): a `case1_unique` check —
`Arc::strong_count(arc) == 1 && Arc::weak_count(arc) == 0` — then `env.get_mut` +
`Arc::get_mut(arc)` mutates the `Vec` **in place**, O(1)/op. Only when the array is aliased
(`strong_count > 1`) does it fall through to the O(N) `Arc::make_mut` clone (`:951`). This is the
existing, already-shipped fix that proves the pattern is known and safe.

**Mutating methods `push`/`pop`/`insert`/`remove`/`extend`/`clear` — has NO fast path at all**
(not merely a less-good one — there is no ownership check anywhere in this path):

1. Method-call dispatch evaluates the receiver unconditionally before it knows what the method is:
   `src/compiler_rust/compiler/src/interpreter_method/mod.rs:149`,
   `evaluate_method_call`: `let recv_val = evaluate_expr(receiver, env, ...)?.deref_pointer();` —
   for an `Expr::Identifier` receiver this clones the `Value::Array(Arc<..>)` out of the
   environment, bumping `strong_count` to at least 2 *before* the method body ever runs.
2. The generic per-type handler does an **unconditional, unchecked copy**:
   `src/compiler_rust/compiler/src/interpreter_method/collections.rs:50-55` (`"push" | "append"`):
   ```rust
   "push" | "append" => {
       let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
       let mut new_arr = arr.to_vec();   // <- unconditional O(N) copy, no strong_count check
       new_arr.push(item);
       Value::array(new_arr)
   }
   ```
   `"pop"` (`:57-66`) does the same — `arr.to_vec()` then `.pop()` — and additionally returns the
   **whole trimmed array** as its result rather than the popped element (a second, distinct
   defect noted in-source, worked around by the write-back layer below for the lvalue case).
3. The lvalue/self-update write-back layer
   (`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:121` —
   `ARRAY_MUTATING_METHODS = ["append","push","pop","insert","remove","extend","clear"]` — and
   `:451-490`, the branch that recognizes `obj_name.push(...)` as a self-mutating call on a bound
   identifier) has **no `strong_count`/ownership check either**: it calls `evaluate_expr(value_expr)`
   (which re-enters step 1/2 above) to get the new array, then unconditionally writes the whole new
   `Arc` back into the binding — `pop` gets its own explicit `arr.to_vec()` here too (`:474`) to
   correctly extract+return the element, same unconditional-copy shape.

So the asymmetry is exactly: **index-store gates its mutation on `strong_count == 1` and mutates
in place when unaliased; the array mutating methods never check ownership at all and always clone
the whole backing `Vec`, whether the array is aliased or not.** That single missing check is the
entire bug. (The sweep's mechanism section described this as "the method's `Arc::make_mut`
always clones" — re-reading the actual code, there is no `Arc::make_mut` call in this path at
all; it's a plain, unconditional `.to_vec()`. Same net effect — always-clone — but the precise
fix target is "add a fast path where none exists," not "extend an existing but overly-conservative
one.")

## Two adjacent, previously-known `push`-related bugs — related plumbing, NOT the same root cause

Both of these involve `.push()` and the same `patterns.rs` self-update write-back subsystem, but
neither is explained by (nor fixed by) the whole-array-clone finding above. Recorded here only to
disambiguate, per the honesty note above:

1. **`self.x.arr.push(v)` on a nested struct field does not persist** (svim jump-list bug,
   2026-05-30; workaround: reassign the whole parent struct instead of mutating the nested field
   array in place). This is a **write-back propagation failure** through multi-level field chains
   in the same `patterns.rs` self-update mechanism — a different failure mode (correctness: the
   mutation is silently lost) than this bug (performance: the mutation succeeds but costs O(N)
   every time). Adjacent subsystem, not the same defect; not fixed by the fast path proposed here
   (that fast path only changes cost for the identifier-receiver case that already write-backs
   correctly).
2. **`arr.push((expr) as u8)` marshals to externs as an empty buffer** (`bug_u8_cast_push_marshalling`,
   2026-05-28: `arr.push(i & 0xFF)` writes correctly, `arr.push((i & 0xFF) as u8)` writes 0 bytes).
   This is a **value-tagging bug at the `[u8]`→extern marshal boundary** — the pushed element's
   `Value` representation differs depending on whether it went through an explicit `as u8` cast,
   and the marshaller mishandles that variant. It reproduces identically regardless of how many
   elements are pushed and is unrelated to whether the whole array gets cloned per push. **Not**
   root-caused by this bug — a genuinely separate defect in a different code path (element
   marshalling, not array mutation dispatch).

## Repro sketch

```
# fill_idx: preallocate + index-assign (O(N) total, O(1)/op)
val n = ...
mut a = [0; n]
for i in 0..n { a[i] = i }

# fill_push: functional/self-mutating push in a loop (O(N^2) total, O(N)/op)
mut a = []
for i in 0..n { a.push(i) }   # or: a = a.push(i)

# Time both for n in {2000, 4000, 8000, 16000}; expect fill_idx ~2x/doubling,
# fill_push ~3.6-3.9x/doubling and diverging (ratio grows with n).
# Full repro scripts (scratchpad, not committed): /tmp/fillcost.spl (this table),
# /tmp/fast.spl (param-read O(1)), /tmp/alias.spl (aliased index-assign O(N)/op),
# /tmp/buildcost.spl (push O(N^2) across element types) — see sweep report for exact contents.
```

## Fix landed (Track A) — 2026-07-07

Implemented and verified. Landed entirely in
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` (the lvalue self-update
write-back branch that recognizes `name.push(...)`/etc. on a bound identifier): arguments are
now evaluated exactly once up front, then the receiver's `Arc<Vec<Value>>` is re-read via
`env.get_mut` and mutated through `Arc::make_mut` — in place when uniquely owned
(`strong_count == 1`), cloned when aliased (`strong_count > 1`) — mirroring the index-store fast
path already shipped at `interpreter/node_exec.rs:906-937`. `collections.rs` (the generic
per-type method handler) is untouched by this fix — it only ever receives already-resolved
arguments/a borrowed slice in this call path and stays pristine; the original fix plan's mention
of gating `collections.rs:50-66` is superseded (see the plan doc's Track A status update for the
full correction).

**Verification performed:**
- **Aliasing:** 15 hand-written aliasing scenarios (two bindings to the same array,
  `mut` params retained by the caller, module globals, captured closure vars) plus the full
  153-file regression corpus — all byte-identical stock-vs-patched output. Value semantics
  preserved exactly; no observed case where an alias saw a mutation it shouldn't have (or vice
  versa).
- **Perf:** O(N²) → O(N) confirmed by direct measurement, not just predicted — ~104× faster at
  N=16000, ~200× faster at N=40000, versus the pre-fix whole-array-clone path. Closes the 84× gap
  vs. `a[i]=`-into-preallocated-local reported above (now roughly at parity, as the fix plan's
  verification protocol required).
- **Scope:** interpret-mode only (`SIMPLE_EXECUTION_MODE=interpret`) — the Rust seed
  interpreter's dispatch path. Compiled/JIT/native-build execution is unaffected.

**One documented, accepted edge case (adversarial review finding, not a regression):**
arguments are evaluated *before* the receiver is re-read via `env.get_mut`, so a self-referential,
trimming-mutating argument on the SAME array — e.g. `a.push(a.pop())`, where evaluating the
argument mutates `a` as a side effect before the outer call re-reads it — observes different
intermediate state than the pre-fix path (which re-entered `evaluate_expr` per call) did. This is
**unreachable in-tree**: a grep across `src/` and `test/` for the same-variable-receiver-equals-
argument-receiver shape returns 0 occurrences; the actual in-tree idiom, `args.push(self.pop())`
(e.g. `src/lib/common/js/engine/vm.spl:197,213`, `:272`), is cross-variable (`args` vs. `self`)
and does not hit this edge. The case is also ill-defined in stock semantics — there is no
independently "correct" answer for what a self-mutating argument to a self-mutating receiver
method should observe. Accepted as documented behavior, consistent with the index-store fast
path's own live-read-before-check semantics (its index/RHS operands are likewise evaluated before
the ownership check). Documented in-source at the fix site so a future reader doesn't mistake it
for an oversight.

**Weak-count invariant (forward-looking note):** the fix uses `Arc::make_mut`, which mutates in
place whenever `strong_count == 1` *regardless* of `weak_count` — this coincides with the sibling
index-store fast path (`node_exec.rs:917`, `Arc::get_mut`, gated by the `strong_count == 1 &&
weak_count == 0` check at `:907`) **only** because no `Value::Array` Arc is ever
`Arc::downgrade`d anywhere in the interpreter today (verified: zero call sites), so
`weak_count` is always 0. If a `Weak` reference on an array Arc is ever introduced, this call
must switch from `Arc::make_mut` to `Arc::get_mut` (falling through to the clone branch on
`None`) to stay safe, exactly like index-store does. Flagged in-source at the fix site.

## Fix plan

See `doc/03_plan/compiler/perf/interp_array_mutating_method_fast_path_plan.md` for the two-track
fix (durable seed fast path vs. immediate per-site refactor) and verification protocol.
