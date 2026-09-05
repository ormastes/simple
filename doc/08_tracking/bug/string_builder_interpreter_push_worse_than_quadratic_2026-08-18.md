# StringBuilder is worse than naive `+` concat in the tree-walk interpreter, and gets worse than O(n^2) as n grows

- Status: LOCALIZED (2026-08-18) — root cause proven, contained fix attempted and found insufficient; see "Verdict" below
- Found: 2026-08-18
- Component: `src/lib/common/string_builder.spl` (`StringBuilder.push`/`.build`),
  interpreter class-method + array-push dispatch
  (`src/compiler_rust/compiler/src/interpreter_method/collections.rs`,
  `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs`)

## Summary

Follow-up on `22faace491c` ("perf(text): adopt array-accumulator + join at 2
sites — to_upper_ascii, svmg disasm"), which adopted `common.string_builder.StringBuilder`
to replace `result = result + c` (documented O(n^2)) accumulation. That commit
was reverted (see below) after measuring both lanes across a range of n instead
of only the original 100-char corpus.

## Measurements (this repo, JIT-seed binary, `bin/simple run` on a standalone
bench comparing `upper_naive` (`+`-concat) vs `upper_sb` (`StringBuilder`) doing
identical ASCII-uppercase work over a synthetic corpus):

### JIT lane (`bin/simple run`, Cranelift):
| n | naive_us | sb_us | sb speedup |
|---|---|---|---|
| 100 | 63 | 68 | 0.93x (roughly break-even) |
| 1000 | 1134 | 506 | 2.2x |
| 5000 | 19339 | 3276 | 5.9x |
| 10000 | 73311 | 8362 | 8.8x |
| 30000 | 627377 | 54006 | 11.6x |

In the JIT lane, `StringBuilder` behaves exactly as intended: naive `+` grows
quadratically (627ms at n=30000), `StringBuilder` stays close to linear (54ms),
crossover is around n~100-300.

### Interpreter lane (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`):
| n | naive_us | sb_us | sb slowdown |
|---|---|---|---|
| 100 | 1160 | 1924 | 1.7x slower |
| 1000 | 12405 | 28715 | 2.3x slower |
| 5000 | 44477 | 344802 | 7.8x slower |
| 10000 | 92430 | 1208713 | 13.1x slower |
| 30000 | 314442 | 10823076 | **34.4x slower** |

In the interpreter, `StringBuilder` is not just constant-overhead-bound at
small n — it gets **relatively worse as n grows**, and its absolute growth rate
is *worse than the O(n^2) baseline it was meant to replace* (naive `+` interp
time grows ~27x from n=100->30000, i.e. sublinear-looking due to other fixed
costs dominating small n; `sb` time grows ~5627x over the same range). This
points to `StringBuilder.push` itself costing more than O(1) amortized per call
in the interpreter — plausibly the interpreter's array `.push()` (or the
class-instance field mutation/method-dispatch path backing it) is not
amortized-O(1) growth, making the "O(n) push + O(n) join" design actually
O(n^2)-or-worse in this lane, with a much higher constant than scalar text
concatenation.

## Root cause (not yet isolated to a single fix site)

Not confirmed by profiling — this needs follow-up. Suspects, ranked by the
measured shape (super-linear-in-n *slowdown ratio*, not just a constant
offset):
1. `[text].push()` in the interpreter reallocates/copies the whole backing
   array per call rather than amortized-doubling growth
   (`interpreter_method/collections.rs`).
2. Per-call class-method dispatch overhead on `StringBuilder.push` (instance
   field lookup/mutation) that itself scales with array size.
3. `.join("")` in `StringBuilder.build()` doing redundant work proportional to
   accumulated size on every intermediate step (unlikely given it's called
   once, but not ruled out).

## Decision: REVERTED

`22faace491c`'s two call sites (`text_ascii.to_upper_ascii`,
`svmg/assembler.disasm`) are reverted back to the original `result = result + x`
form in a follow-up commit, because:
- `bin/simple test` (the lane most of this codebase's specs and tooling run
  under, see `.claude/rules/testing.md`: "`bin/simple test` hard-defaults to
  the tree-walk interpreter") would see call sites get **dramatically slower**,
  not faster, from this "fix" — regressing real usage, not a benchmark
  artifact.
- The JIT-lane win is real but does not offset the interpreter-lane loss for
  library code whose caller engine is not controlled by the callee.
- `StringBuilder` itself needs a perf fix in the interpreter lane before it is
  safe to adopt as the general-purpose "avoid O(n^2) concat" remedy this
  codebase's other bug docs (C-MIG-0023, C-MIG-0035, base64_encode) point to.

## Follow-up required before StringBuilder is re-adopted anywhere

1. Profile/isolate why `StringBuilder.push` costs more than O(1) amortized per
   call in the interpreter (see suspects above).
2. Fix the interpreter-side array push (or class-method dispatch) cost.
3. Re-run this exact bench (`upper_naive` vs `upper_sb`) in the interpreter
   lane and confirm sub-quadratic scaling before re-adopting.
4. Only then re-apply the `to_upper_ascii`/`svmg/assembler.disasm` change,
   updating `test/01_unit/lib/common/text_ascii_to_upper_crosslang_spec.spl`'s
   perf_evidence corpus to a size (>=5000) where the win is real and
   documented, in both lanes.

## Verdict (2026-08-18 follow-up)

### Independent repro (minimal harness, not the uppercase bench)

Standalone `Bucket { items: [i64] }` class with `fn push_one(mut self, x: i64):
self.items.push(x)` called in a loop, `SIMPLE_EXECUTION_MODE=interpreter
bin/simple run`, this repo's deployed seed:

| n | wall time |
|---|---|
| 1000 | 0.08s |
| 3000 | 0.13s |
| 10000 | 0.61s |
| 30000 | 4.66s |

30x growth in n -> ~58x growth in time: confirms worse-than-linear, consistent
with the StringBuilder bench's finding, and isolates the defect to array
`.push()` through a CLASS FIELD (`self.items.push(x)`), independent of
`StringBuilder`/text/`.join()` — i.e. it is a general interpreter defect, not
specific to `StringBuilder`. Same shape under
`SIMPLE_EXECUTION_MODE=jit`: flat at 0.07s across all four n (JIT lane
unaffected, matching the original bench).

### Root cause #1 (proven): generic array-method dispatch clones the whole backing Vec per push

`src/compiler_rust/compiler/src/interpreter_method/collections.rs:179-184`,
`handle_array_methods`'s `"push" | "append"` arm:

```rust
"push" | "append" => {
    let item = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
    let mut new_arr = arr.to_vec();   // <-- O(n) clone of the ENTIRE backing Vec
    new_arr.push(item);
    Value::array(new_arr)
}
```

This handler only ever receives a borrowed `&[Value]` slice (it cannot mutate
in place), so it always clones. That is intentional and fine for genuinely
read-only calls, but it is also the path every deep-place mutating method call
falls through to
(`interpreter_method/mod.rs:1863`, `evaluate_method_call` ->
`handle_array_methods`) whenever the receiver is not a bare local identifier —
in particular `self.field.push(x)`, i.e. any array stored in a class field,
which is exactly how `common.string_builder.StringBuilder` accumulates
(`self.items.push(item)` internally). The bare-identifier case (`arr.push(x)`
where `arr` is a plain local variable) already has its own O(1)-amortized
`Arc::make_mut` fast path
(`interpreter_helpers/patterns.rs:646-826`), so this defect specifically
affects field/nested-place pushes, not all pushes.

### Root cause #2 (proven by regression, not by design intent): a deliberate ownership-sharing choice defeats any local fix at the field-push site

An `Arc::make_mut`-based fast path for deep places was implemented (mirroring
the identifier fast path) — `push_at_place` in
`src/compiler_rust/compiler/src/interpreter/place.rs`, wired into the "General
PLACE receiver" branch in
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` (~line 529),
navigating to the array via `env.get_mut(&place.root)` +
`project_mut(...)` and pushing directly on the `Arc<Vec<Value>>` without any
whole-Vec clone in the success case.

**This compiled clean (`cargo check --release --bin simple`) and built clean,
but made the SAME harness SLOWER, not faster: n=30000 went from 4.66s (before)
to 11.25s (after)**, measured against a locally-built seed
(`CARGO_TARGET_DIR` under `/mnt/data`, never the deployed `bin/simple`).

Why: `interpreter_helpers/patterns.rs`'s identifier-receiver fast path (the
one that dispatches `acc.push_one(i)` to the `Bucket` method body, ~lines
578-588) deliberately does this on every such call:

```rust
// Take ownership: Arc refcount drops to 1 → zero-copy mutations.
// IMPORTANT: args must be evaluated in env while `self` is still
// present. We remove `self` for the zero-copy optimisation, but
// re-insert a clone so that arg expressions such as `me.field`
// ... can still resolve during bind_args ...
if let Some(Value::Object { class, fields }) = env.remove(obj_name) {
    env.insert(obj_name.to_string(), Value::Object { class: class.clone(), fields: Arc::clone(&fields) });
    match find_and_exec_method_with_self_owned(method, args, &class, fields, ...) { ... }
}
```

The `Arc::clone(&fields)` re-inserted into the CALLER's environment stays live
for the **entire duration of the call**, including the whole body of
`push_one`/`StringBuilder.push`. So inside that body, `self`'s `fields` Arc
has refcount >= 2 (one held by the caller's re-inserted copy, one owned by the
callee) for the whole call — `Arc::make_mut(fields)` inside `push_at_place`
therefore ALWAYS clones the fields `HashMap` (cheap: it is `Value` clones,
i.e. `Arc::clone`s, for each field — O(field count), not O(array size)), but
that clone gives `items` a NEW distinct entry in the map while the OLD map
(still referenced by the caller's aliased copy) still points at the SAME
`items` Arc. That leaves `items` itself with refcount 2 at the moment
`push_at_place` reaches it, so `Arc::make_mut(items)` clones the **whole
backing Vec** anyway — the identical O(n)-per-push cost the generic path
already paid, plus the added HashMap-walk/clone overhead on top, which is why
the "fixed" build measured slower, not faster.

This is not a defect introduced by the attempted fix; it is a **pre-existing,
deliberate design choice** (the comment states its purpose explicitly: let
argument expressions like `me.field` resolve against the caller's own `self`
during arg evaluation) that happens to also pin the refcount for the entire
method body, not just argument evaluation. Any local fix at the push call
site — however implemented — is undermined by this upstream aliasing for as
long as that re-insertion lives past argument evaluation.

### Attempted fix: REVERTED

The `push_at_place` fast path and its call site were reverted from
`src/compiler_rust/compiler/src/interpreter/place.rs` and
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` (`git
checkout --`) after the regression was measured — landing a change that makes
the documented defect worse is not an acceptable outcome, and the repo's git
status showed unrelated concurrent-session changes in the same tree that must
not be disturbed.

### Proposed patch sketch (NOT implemented — for the next attempt)

1. In `interpreter_helpers/patterns.rs`'s identifier-receiver zero-copy branch
   (~line 578-606), narrow the re-inserted `Arc::clone(&fields)` caller-side
   binding to the **argument-evaluation window only**: evaluate all `args`
   eagerly against an env that still has the caller's `self` visible, THEN
   `env.remove(obj_name)` again (drop the caller-side alias) BEFORE calling
   `find_and_exec_method_with_self_owned`, then re-insert the method's
   returned `updated_self` as the final value. This preserves today's
   "`me.field` resolves during arg binding" behavior while giving the callee's
   `self.fields` Arc a true refcount of 1 for the body of the call, which is
   the precondition `push_at_place` (or even the existing generic path, if it
   is later made place-aware) needs to be O(1) amortized.
   Risk: `find_and_exec_method_with_self_owned`'s current call shape and any
   other caller relying on the caller-side alias staying live through the
   whole call would need re-auditing — this touches a shared, deliberately
   documented ownership-transfer mechanism used by every Object method call,
   not just push.
2. Re-apply the `push_at_place`/place.rs fast path from this investigation on
   top of (1) once the refcount precondition holds, and re-run the harness
   above to confirm O(1)-amortized push before considering it fixed.
3. Only then revisit `StringBuilder` re-adoption per the original "Follow-up
   required" list below.

### Containment verdict: NOT CONTAINED

The defect has TWO independent causes that must both be addressed for a real
fix: (1) the generic array-push clone (`collections.rs:179-184`, contained,
single-arm), and (2) the caller-side self-aliasing window
(`patterns.rs:578-606`, a shared mechanism affecting every Object method
call, not contained to push). Fixing only (1) — which is what was attempted —
is provably insufficient (measured regression) because of (2). Per the task
instructions this is recorded as LOCALIZED, not fixed, with the patch sketch
above for the next attempt.

### Fix-test spec

`test/01_unit/lib/common/array_field_push_interpreter_perf_spec.spl` —
correctness assertions (full-count push, aliasing via a second binding,
nested-array element pushes) all PASS today against the deployed seed; it
documents the perf defect and the reverted-fix investigation in its header
comments rather than asserting an inline timing ratio (no portable
high-resolution timer is threaded through this spec harness lane), per this
doc's measured evidence above serving as the timing record instead.

## Related
- `22faace491c` (reverted commit)
- Bug C-MIG-0035 (original `to_upper_ascii` O(n^2) finding)
- `src/lib/common/string_builder.spl` — `RtStringBuilder` (runtime-backed,
  amortized O(1) push via a Rust-heap `String`) is a DIFFERENT type in the same
  file and was not exercised by this bench; it may not share this defect since
  it bypasses the Simple-level array entirely. Worth trying as the interpreter
  remedy in the follow-up above instead of fixing array-`StringBuilder`.
