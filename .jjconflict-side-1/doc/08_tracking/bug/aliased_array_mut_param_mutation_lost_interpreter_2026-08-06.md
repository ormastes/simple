# Passing one array as both a `mut` and a non-`mut` parameter silently discards the mutation (interpreter)

- **Filed:** 2026-08-06
- **Status:** Investigated, not fixed (blocked — see "Investigation update" below). Precisely
  localized to a specific function in the out-of-scope Rust seed (see "Not yet done" → now done,
  below); every reachable pure-Simple candidate interpreter was checked and does not share this
  defect, but none is buildable/runnable in this tree today, so no bounded, verifiable fix location
  exists yet.
- **Severity:** High — silent wrong answer, no error, no crash, no warning
- **Component:** tree-walk interpreter — argument aliasing / array value semantics
- **Engine:** `SIMPLE_EXECUTION_MODE=interpret` **and `bin/simple test`**. The JIT is correct.
- **Found by:** lane P0, writing the memmove-semantics test for `oracle_copy_span`

## Symptom

When the *same* array is passed to a function as both a `mut` parameter and a
plain (non-`mut`) parameter, every write through the `mut` parameter is **lost**
under the interpreter. The call returns normally; the array is simply unchanged.

```
oracle_copy_span(mut dst: [u32], dst_offset, src: [u32], src_offset, count)
...
oracle_copy_span(e, 4, e, 0, 12)     # e is BOTH dst and src
```

Measured on the Rust bootstrap seed `bin/release/x86_64-unknown-linux-gnu/simple`
(md5 `ed53cc5f255e269ca27c4cd83b17aef9`), `e` initialised to `[1..16]`:

| engine | `e[4]` | `e[15]` | FNV-1a of the span | verdict |
|---|---|---|---|---|
| JIT (`bin/simple run`) | 1 | 12 | 280943671307053 | correct — memmove semantics |
| `interpret` | 5 | 16 | 221120998044693 | **array completely unchanged** |
| `bin/simple test` | — | — | same as `interpret` | **unchanged** |

The reverse-direction call `oracle_copy_span(f, 0, f, 4, 12)` behaves
identically: correct under the JIT, wholly unapplied under the interpreter.
Both interpreter hashes equal the hash of the untouched input, which is the
cleanest available proof that *nothing* was written — not that something wrong
was written.

## Why this is not the known array-value-semantics rule

Arrays being value types explains why `src` would be a *snapshot*. It does not
explain why writes through `dst` vanish. A value-copied `src` with a live `dst`
would still produce a correct non-overlapping copy — in this fixture it would
produce exactly the same answer the JIT gives, because memmove semantics are
defined as "read the whole source before writing". Instead the destination is
untouched, so the `mut` binding itself is not writing back when the same
underlying array is also bound to another parameter.

This is also distinct from the class-field divergence filed the same day
(`class_field_reference_semantics_diverge_2026-08-06.md`): that one is about
class instances in fields; the fn-parameter row of its truth table is REF on
both engines. This is arrays, and only when aliased across two parameters.

## Why it matters beyond one kernel

`scroll_rect` is self-copy by definition — scrolling a window moves a region
within one framebuffer. Any implementation written the obvious way
(`copy(fb, dst_row, fb, src_row, n)`) is a **silent no-op under the interpreter
and under `bin/simple test`**. A spec asserting post-scroll pixels fails with a
confusing diff; a spec asserting only that the call returned **passes
vacuously**. Given that the WM render lane is currently interpreter-bound in its
entirety (see `doc/09_report/render_pipeline_profile_2026-08-06.md`), this is
the engine that would actually run it.

## Repro

`oracle_copy_span` in `src/lib/common/gpu/engine2d/scalar_oracle.spl`, exercised
by the two aliased examples in
`test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl`. Run the same
call under `bin/simple run` and under `SIMPLE_EXECUTION_MODE=interpret`.

## Status of the affected spec

The two aliased examples **pin the current interpreter behaviour** with loud
`TODO(aliased-mut-param)` markers naming the contract values, because the spec
runner cannot express expected-fail. They flip red when this defect is fixed,
which is the intent. The kernel's direction logic is *not* in doubt — the JIT
row above shows it satisfies the contract exactly.

## Not yet done

- Not localized. The measured failure is in the Rust seed, which is out of scope
  by policy; whether the pure-Simple MIR interpreter shares the behaviour is
  unknown (no pure-Simple binary exists in this tree).
- Not determined whether this extends to two `mut` parameters bound to the same
  array, or to structs/classes passed the same way.
- No audit yet of existing call sites that alias one array across two
  parameters. That sweep should happen before anyone relies on self-copy.

## Related

- `class_field_reference_semantics_diverge_2026-08-06.md` — sibling divergence,
  different construct, filed the same day.
- The contract this violates: `doc/04_architecture/ui/rendering/exact_8bit_pixel_formula.md` §6.

## Investigation update (2026-08-06, second pass)

### Localization (fills in the "Not yet done" gap above)

Root cause is now precisely localized, not just "in the Rust seed":

- **Arg-binding entry:** `src/compiler_rust/compiler/src/interpreter_call/core/arg_binding.rs`
  — `bind_args` / `bind_args_with_injected` (~lines 78–409) evaluate call-site
  `Argument`s into the callee's local env. No mut/write-back logic lives here.
- **The actual bug site — write-back (copy-out):**
  `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`,
  `write_back_mutable_arguments` (~lines 969–1105; doc comment at 957–968
  references "Bug #19"), called from `exec_function_with_captured_env` (~917),
  `exec_function_inner`'s callers (~1195), and
  `exec_function_with_values_and_writeback_inner` (~1260).

**Mechanism:** `write_back_mutable_arguments` walks the *original call-site
argument list in order*. For every identifier-bound argument whose
callee-local value is a container (`Value::Array | Dict | Object | Tuple`,
~1066–1074) it unconditionally does
`outer_env.insert(caller_name, callee_val.clone())` — it does **not** check
`Parameter.mutability` (a real field, `ast/nodes/core.rs:327`) before writing
back. The assumption baked in is that re-writing a non-`mut` param's
(unchanged) local binding back to the caller is a harmless no-op. That
assumption breaks exactly under aliasing: `oracle_copy_span(mut dst: e, ...,
src: e, ...)` binds the same caller array `e` to two callee-local names,
`dst` and `src`. Arrays are `Arc`-backed with copy-on-write, so mutating
`dst` allocates a new `Arc` only in the `dst` slot; `src` still points at the
pristine original. The write-back loop first writes the mutated `dst` array
back into `outer_env["e"]` (correct), then reaches the later `src` argument
and unconditionally writes the still-pristine `src` value into the *same*
`outer_env["e"]`, clobbering the mutation. Last-write-wins across multiple
argument names that alias one caller variable, with no mut/non-mut
distinction in the write-back predicate, is the defect. (Investigated via a
read-only Explore pass over `interpreter_call/core/`; no edits made — see
scope note below.)

A theoretically bounded, in-scope-if-Rust-were-allowed fix would be: only
write back arguments whose corresponding `Parameter.mutability` is `mut`, and
skip non-`mut` container arguments in `write_back_mutable_arguments`
entirely — non-`mut` params never need copy-out, aliased or not, so this also
can't regress the non-aliased case. Not attempted here; `src/compiler_rust/**`
is out of scope by this repo's standing policy (fix `.spl`, not Rust) and by
this bug's own original scope note above.

### Pure-Simple candidates checked (none reproduce this defect)

Same three tiers reviewed as for the sibling class-identity bug
(`class_field_reference_semantics_diverge_2026-08-06.md`):

1. **`src/compiler/10.frontend/core/interpreter/eval_calls.spl`** — the
   function-call parameter-binding loop (~line 332 onward) copies **only**
   value-type structs (`val_struct_deep_copy`, gated by
   `interp_struct_is_value_type`); it never copies arrays at param-bind time
   at all, for `mut` or non-`mut` params alike. Consequently a call that
   passes the same array as both `dst` and `src` binds *both* parameter names
   to the identical arena `value_id` — there is no separate write-back step
   to get wrong, because nothing was ever copied apart in the first place.
   Reads/writes through either binding hit the same
   `val_arrays[value_id]` slot (see `eval_assign_expr`'s `EXPR_INDEX` branch
   and `eval_index_expr`), so `oracle_copy_span`'s own direction-aware
   in-place algorithm (descending when `dst_offset > src_offset`, already
   confirmed correct — the JIT row proves the kernel logic itself is fine)
   would execute against genuinely shared memory, structurally immune to
   this bug. This is an existing property of the representation, not a
   change made in this pass.
   - Note: this also means this tier does **not** currently implement
     "plain (non-`mut`) array param = value-copy" at all — arrays are always
     aliased there. That is a separate, pre-existing gap from what's spec'd
     for ordinary (non-aliased) array parameter passing, out of scope for
     this bug (which is specifically about a *mutation being silently lost*,
     not about over-sharing) and not touched here.
   - Same unreachability caveat as the sibling doc: this tier requires a
     compiled self-hosted binary to exercise via its real entry points
     (`core_interpret`), which does not exist in this tree
     (`jit_init_with_backend` unresolved). Not independently re-verified
     dynamically for this bug beyond the reasoning above.
2. **`src/compiler/95.interp/mir_interpreter.spl`** — arrays/aggregates are
   materialized once via `Aggregate` into the flat `locals: {i64: i64}`
   address space; any two names bound to "the same array" would hold the same
   base-address `i64`, so `GetField`/`SetField`/element access resolve
   through the identical memory — no separate mut/non-mut copy-out step
   exists to have this bug in the first place.
3. Not re-checked separately for this bug: `src/compiler/70.backend/backend/objects.spl`
   (`ObjectStore`) is class/object-handle-focused (task #112); this bug is
   array-specific and that tier's existing spec doesn't cover arrays.

### Conclusion

Root cause is now fully localized (file, function, and line-accurate
mechanism) but remains in Rust code that is out of scope by explicit policy
(stated in this doc's own header and confirmed against repo/session standing
practice). Every pure-Simple interpreter candidate that exists in this tree
was checked and does not reproduce this defect by construction — but none of
them is reachable/buildable today without a full self-hosted bootstrap, so
there is no bounded, verifiable place in-scope to land a fix or a real
fail-before/pass-after regression spec. The two `TODO(aliased-mut-param)`
examples in `test/01_unit/lib/common/gpu/engine2d/scalar_oracle_spec.spl`
(lines ~279–302) remain the correct executable pin of current (broken)
behavior and were left untouched. Leaving Status as blocked/investigated
rather than claiming a fix.
