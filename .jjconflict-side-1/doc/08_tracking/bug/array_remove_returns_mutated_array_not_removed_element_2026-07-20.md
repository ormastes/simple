# `array.remove(index)` returns the mutated array, not the removed element

**Status:** FIXED IN SOURCE 2026-08-08 — both lanes. `.remove(index)` now returns
the removed element and mutates in place on the interpreter AND the compiled
lanes. `mutable_by_default_spec.spl` went 21/24 -> **24/24** (both copies).
Guard: `scripts/check/check-array-remove-returns-element.shs`. Red against the
stale deployed `bin/simple` until the next seed redeploy. See "Fix 2026-08-08".
**Date:** 2026-07-20
**Component:** Array `.remove(index)` builtin method (interpreter),
exercised via `test/feature/usage/mutable_by_default_spec.spl`.
**Severity:** Medium — 3 of 24 examples fail; every other mutable-array
operation in the same file (`insert`, `clear`, index-assignment) is
correct.

## Symptom

```
✗ allows remove on default arrays
  expected [1, 3] to equal 2
✗ allows remove first element
  expected [2, 3] to equal 1
✗ allows remove last element
  expected [1, 2] to equal 3
```

```simple
it "allows remove on default arrays":
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    expect removed == 2
    expect arr.len() == 2
```

`arr.remove(1)` is expected to return the removed element (`2`, the value
at index 1), matching common `Vec::remove`/`list.pop(index)`-style
conventions and the spec's own naming (`val removed = ...`). Instead it
returns the array itself, post-removal (`[1, 3]`) — the mutation itself is
correct (dropping index 1 from `[1, 2, 3]` does yield `[1, 3]`), only the
*return value* is wrong: the method returns the mutated collection instead
of the removed element.

This is NOT a stale-test issue: the spec's expectation (`removed == 2`) is
the conventional, documented-sounding semantics for a `.remove(index)`
method, and no other array method in this same file has this problem —
`.insert(index, value)` (tested without capturing its return value, only
checking the mutated array afterward) and `.clear()` both pass fine. Per
this triage pass's fix guide, a prior pass explicitly declined to touch
this spec because "fixing" it would require weakening/redirecting the
`.remove()` return-value assertion — left correctly RED here as well.

## Minimal repro

```simple
fn main():
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    print(removed)
    print(arr)

main()
```

Expected: `2` then `[1, 3]`. Actual: `[1, 3]` printed for `removed` too
(i.e. `.remove()`'s return value equals the post-mutation array, not the
removed element).

## Root-cause hypothesis

Not traced into interpreter source (out of scope for a spec-triage pass;
needs a rebuild to verify any fix). Candidate: the `.remove(index)` builtin
method arm returns `self` (or the receiver's post-mutation `Value`) instead
of the element it spliced out — a likely copy-paste/API-shape mismatch
against `.insert()`'s (correctly void/self-returning) arm, or against
`Dict.remove(key)`'s convention if that method returns something
different.

## Notes

- Do NOT attempt a Rust seed source fix here (out of scope for a
  spec-triage pass; needs a rebuild to verify).
- Per the fix guide's explicit hard rule, the spec's assertions
  (`expect removed == 2` etc.) were NOT weakened, narrowed, or redirected
  to match the actual (wrong) return value — all 3 examples are left
  correctly RED.

## Affected specs

- test/feature/usage/mutable_by_default_spec.spl (3 of 24 examples: `allows
  remove on default arrays`, `allows remove first element`, `allows remove
  last element`)

Verified with:
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/mutable_by_default_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
→ `Passed: 21, Failed: 3`

## Re-triage 2026-08-08 — still OPEN, and the JIT lane is worse than filed

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the Rust bootstrap-seed banner. No pure-Simple self-hosted binary is
deployed on this host, so both lanes below are seed lanes.

This report's own minimal repro, run unchanged:

```simple
fn main():
    var arr = [1, 2, 3]
    val removed = arr.remove(1)
    print "removed={removed}"
    print "arr={arr}"
main()
```

| lane | `removed` | `arr` after |
|------|-----------|-------------|
| interpreter (`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`) | `[1, 3]` | `[1, 3]` |
| seed JIT (`bin/simple run`, the default) | `nil` | `[1, 2, 3]` |

**Interpreter:** exactly as filed — the return value is the mutated array
instead of the removed element `2`, while the mutation itself is correct. No
change since 2026-07-20.

**Seed JIT — new, not in the original report:** `.remove(index)` returns `nil`
*and the array is not mutated at all*. So on the engine ordinary programs run
on, `arr.remove(1)` is a complete no-op that also discards the element it was
supposed to return. That is strictly worse than the interpreter behaviour and
is a second, independent defect in the same builtin.

Note the discovery asymmetry: `bin/simple test` runs the interpreter, so the
three RED examples in `mutable_by_default_spec.spl` document only the return
value bug. Nothing in the spec corpus can observe the JIT no-op, because the
suite cannot reach that engine — the structural gap catalogued in
`run_vs_test_harness_divergence_2026-07-28.md`.

**Still not fixed here, and the spec stays RED.** Per this repo's testing rule
a correct spec that fails is a legitimate artifact; `expect removed == 2` is the
right assertion and must not be weakened. Closing this needs a decision on the
contract (return the removed element, as the spec and the `Vec::remove` /
`list.pop(index)` convention say) applied to BOTH lanes, plus the JIT mutation
fix which is a separate, larger problem.

## Fix 2026-08-08 — contract settled, both lanes corrected

### The contract, and why

**`array.remove(index)` removes the element at `index` IN PLACE and RETURNS THAT
ELEMENT.** There is no prose spec for it anywhere in `doc/`, so the contract was
settled from the tree's own primary sources, which converge:

- sibling `pop()` — `rt_array_pop` mutates in place and returns the ELEMENT;
  `method_registry/builtins.rs` declares it `is_mutating: true`; HIR types
  `[T].pop()` as `T`.
- sibling `Dict.remove(key)` — `rt_dict_remove` removes the entry and returns the
  VALUE; HIR types it as the dict's value type.
- `method_registry/builtins.rs` already declared array `remove` as
  `is_mutating: true`, "removes element at index".
- `mutable_by_default_spec.spl` asserts exactly `removed == 2` and
  `arr.len() == 2`.

The rejected alternative — "return the mutated array", what the AST interpreter
did — had no runtime implementation, no HIR type, and no spec behind it, and
contradicts both siblings. It was a defect, not a design.

### Root causes — FIVE, not one

1. **Interpreter returned the receiver.** `interpreter_method/collections.rs`
   `"remove"` returned `Value::array(new_arr)` instead of the spliced element.
2. **`rt_array_remove` DID NOT EXIST.** The method registry had referenced the
   symbol all along; nothing implemented it. Codegen's name-keyed table mapped
   `remove` to `rt_dict_remove` for EVERY receiver, and that function type-checks
   its receiver as a Dict — on an Array it early-outs, returns NIL, mutates
   nothing. That is the whole "JIT is worse" half: a total no-op.
3. **Write-back would have been dropped.** The interpreter propagates a mutation
   only when the result's discriminant MATCHES the receiver's. Changing `remove`
   to return an element makes `Int` vs `Array` never match, so the removal would
   have been silently discarded for every field/index place — the exact trap
   `pop` already had a special case for. `remove` needed the same.
4. **Missing HIR return type.** Array `remove` was absent from the HIR
   method-return-type table, so it fell through to `TypeId::ANY` and no unboxing
   was selected: the element came back still TAGGED. Measured through a typed
   field: **56 instead of 7** (7 << 3).
5. **Missing MIR unbox.** Typing it in HIR is necessary but NOT sufficient — the
   HIR type only SELECTS the unbox. Without adding `remove` to the
   slot-yielding-accessor family in `mir/lower/lowering_expr_method.rs`, locals
   showed **160 instead of 20** (20 << 3).

Causes 4 and 5 are the same class already documented in that table for
`index_of` and `sum`. `pop` was correct only because it was listed in both places.

### Files

- `src/compiler_rust/runtime/src/value/collections.rs` — new `rt_array_remove`
  (all three storage layouts: tagged, byte-packed, u64-packed; out-of-range is a
  no-op returning NIL, never a panic — unwinding across `extern "C"` from JIT
  code is UB) and `rt_collection_remove`, the receiver-dispatching entry point.
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` — register both.
- `codegen/instr/closures_structs.rs` + `codegen/llvm/functions.rs` — route the
  `remove` METHOD to `rt_collection_remove` on both compiled backends.
- `interpreter_method/collections.rs`, `interpreter_method/mod.rs`,
  `interpreter_helpers/patterns.rs` — element return + write-back on both the
  in-place fast path and the clone-then-mutate slow path.
- `hir/lower/expr/mod.rs`, `mir/lower/lowering_expr_method.rs` — typing + unbox.

### Near-miss worth recording: `rt_remove` was already taken

The dispatcher was first named `rt_remove`. That collides with
`int64_t rt_remove(const char *path)` — the POSIX **file-deletion** wrapper in
`src/runtime/runtime_hosted_fs.c`. The link failed loudly
(`rust-lld: error: duplicate symbol`), which is the good outcome: this repo
builds some link steps with `-z muldefs`, under which the linker would have
silently picked one definition and either sent `arr.remove(i)` into `unlink()`
or sent file deletions into the collection helper. Renamed to
`rt_collection_remove`.

### Evidence, both directions

`scripts/check/check-array-remove-returns-element.shs`, per engine: the return
value is the removed ELEMENT; the receiver SHRANK (catches the JIT no-op, which
left `len` at 3); the CORRECT element went (an off-by-one that pops the tail
would satisfy the first two otherwise); first/last index; out-of-range is a
no-op and not a crash; and a TYPED FIELD receiver returned through a declared
`-> i64`, which is a different code path that caught cause 4 after all the
local-variable cases already passed.

    # RED — stale deployed bin/simple:
    FAIL — engine 'interpreter': ... expected 'mid=20', got: mid=[10, 30]
    # (JIT half of the same run: mid=nil, mid_len=3)

    # GREEN — freshly built seed:
    PASS — 2 engine setting(s) checked: interpreter,jit — array.remove(index)
    returns the removed element and shrinks the receiver in place

Intermediate RED states are themselves evidence the guard discriminates: `mid=nil`
(no dispatcher), then `mid=nil` for indices 1,2 while `mid_0` worked (missing
tag on the index — index 0 works because the INT tag is 0, the signature of that
bug), then `field_got=56`, then `mid=160`. Each was a real build.

Spec: `mutable_by_default_spec.spl` **21/24 -> 24/24** on both copies
(`test/03_system/feature/usage/`, `test/feature/usage/`), `dropped=0`. The three
originally-RED examples were correct all along and were never weakened.

**Not yet closed:** `bin/release/<triple>/simple` predates this fix, so the guard
is red until the next seed redeploy.
