# Seed interpreter: `text.bytes()` u8 elements compare wrong via `<=`/`>=` (BoxInt tag-shift)

- **Date:** 2026-07-17
- **Area:** `src/compiler_rust` seed interpreter (bootstrap seed only — `src/compiler_rust/target/release/simple`).
  NOT reproduced as a duplicate_check bug; found while root-causing an apparent
  `duplicate-check` token-mode detection failure (see
  `doc/08_tracking/bug/duplicate_check_cosine_quadratic_timeout_2026-07-01.md`
  sibling investigation, task: worker_O_dup_sanity).
- **Severity:** high (silently corrupts any code that does relational
  comparison — `<=`, `>=`, `<`, `>` — on a byte pulled out of `text.bytes()`
  against an integer literal, with no error/crash).
- **Status:** FIXED (worker Q, 2026-07-17). Related to (but not
  the same code path as) `test_runner_expect_failure_swallowed_u8_bytes_2026-07-03.md`
  (test-runner matcher, `bytes[44] == 99u8`, still open) and
  `baremetal_u8_index_equality_2026-05-30.md` (native/freestanding codegen
  `[u8]` indexing, fixed 2026-05-30 — different code path, does not cover
  this interpreter case).

## Root Cause (worker Q)

Not in the JIT relational-op codegen, and not in `bytes()` element
production. `bin/simple run` on the seed defaults to `ExecutionMode::Jit`
(Cranelift), and `SIMPLE_EXECUTION_MODE=interpret` on the SAME repro proves
the tree-walking interpreter is unaffected (all values correct) — this bug
is Cranelift-JIT-only, and the mechanism is a **HIR method-call return-type
inference gap**, the exact same class of bug (and exact same match table)
as `jit_string_length_var_control_flow_wrong_value_2026-07-17.md` fixed
earlier the same day.

`lower_builtin_method_call`'s string-methods `result_ty` match arm in
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` recognized `len`,
`length`, `starts_with`, `ends_with`, `contains`, `concat`, `slice`,
`replace`, `find`, `index_of`, `find_str`, `rfind`, `last_index_of` — but
NOT `bytes`. So `s.bytes()` fell through to the generic dynamic-dispatch
path, which (finding no user-defined `.bytes` method — `.bytes()` is a pure
Rust builtin, no `.spl` stdlib definition) returned `TypeId::ANY` as its
final fallback, instead of `[i64]`.

That wrong static type broke `byte_arr[idx]` in
`mir/lower/lowering_expr_struct.rs`: the array-index lowering only emits
`UnboxInt` (untagging a loaded `RuntimeValue` — `(v << 3) | TAG_INT` — into
a native i64) when the STATICALLY KNOWN element type is a concrete int type
(`needs_int_unbox` gated on `element_expr_ty`). With `element_expr_ty ==
ANY`, the raw tagged `RuntimeValue` returned by `rt_array_get` was passed
through unchanged (`// Strings, arrays, objects are already usable as
pointers` fallback) — correct for genuinely ANY-typed values, but wrong
here since the underlying element really is a native int that downstream
code treats as already-unboxed.

**Operator audit** (`b = "a\u{2014}b".bytes()[0]`, true value 97; JIT,
before fix):

| Op | Result | Correct? | Why |
|----|--------|----------|-----|
| `==` / `!=` | correct | YES | `compile_binop`'s `Eq`/`NotEq` arms check `vreg_is_native_equality_scalar`; for a non-native-scalar (ANY) operand they fall back to the safe `rt_native_eq` runtime call, which unboxes correctly regardless of tag. |
| `<`, `<=`, `>`, `>=` | wrong (or "right" by coincidence) | NO (uniformly) | `compile_binop`'s `Lt\|Gt\|LtEq\|GtEq` arm has NO such safe fallback — always emits a raw Cranelift `icmp` assuming both operands are already native untagged i64s. Comparing tagged `776` (`97<<3`) against untagged literal `97`/`122` gives answers that only coincidentally match the true relation for `>=`/`<` at these specific operands; `<=`/`>` are visibly wrong. |
| `+`, `-` | garbage (`<invalid-heap:...>`, `<value:0x...>`) | NO | Raw `iadd`/`isub` on `776` shifts the low 3 tag bits away from `TAG_INT` (`776+1=777`, `777 & 7 = 1`), so the print-any routine misdecodes the result as a different runtime kind (heap pointer). |
| `*` | correct by coincidence | N/A | `776 * 2 = 1552 = (97*2) << 3` — multiplying a `TAG_INT`-tagged value (tag bits `000`) by 2 happens to preserve the tag-zero invariant AND scale the payload correctly; not a general property, just numerically lucky for this operand. |

So the task's premise ("audit relational vs arithmetic separately") actually
resolves to a single root cause: **all of the above were symptoms of one
wrong static type**, not independent per-operator defects. Fixing the type
inference fixed every operator uniformly (verified below) — no separate
relational-op or arithmetic-op fix was needed, and `compile_binop`'s
asymmetric Eq/relational safety handling, while itself an interesting
latent gap for genuinely-ANY-typed ints, was not touched (out of scope: it
never miscompiles when the static type is correct, which is now always the
case for `.bytes()` elements).

## Fix

Added a `"bytes"` arm to the SAME string-methods table, registering the
correct `[i64]` array type:
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` (`lower_builtin_method_call`),
marker `seed_bytes_u8_boxtag_2026-07-17`. This lets the existing
`needs_int_unbox` / `UnboxInt` machinery in
`mir/lower/lowering_expr_struct.rs` do the right thing automatically — no
codegen or runtime changes were needed.

Regression test (Rust): `bytes_method_infers_i64_array_seed_bytes_u8_boxtag_2026_07_17`
in `src/compiler_rust/compiler/src/hir/lower/tests/expression_tests.rs`,
asserting `s.bytes()` infers `Array{element: I64}` (not ANY) and
`byte_arr[0]` infers `I64`. Confirmed fails without the fix (HIR type is
`ANY`, `TypeId::Array` match arm panics) and passes with it.

End-to-end verification (fresh seed rebuild, isolated `CARGO_TARGET_DIR`):
the doc's minimal repro now prints `c=97` (was `776`) and `b <= 122 -> true`
(was `false`) with NO `int(...)` wrapper needed. A broader operator audit
(`==`,`!=`,`<`,`<=`,`>`,`>=`,`+`,`-`,`*`) all match the interpreter's
reference values post-fix.
`timeout 240 <fixed-binary> test test/01_unit/app/cli/duplicate_check_unit_spec.spl`
exits 0, including the specific tokenizer test
"classifies control-flow and binding keywords as Keyword tokens" that
exercises the exact `bytes[i]` classification pattern this bug corrupted.

## Symptom

A byte read from `text.bytes()` prints correctly, but a relational comparison
against a plain `i64` literal gives the wrong answer, and an explicit
`val c: i64 = b` annotation does NOT fix it — only `int(b)` does.

Minimal repro (`bin/simple run` on the seed, `src/compiler_rust/target/release/simple`):

```simple
fn main():
    val s = "a\u{2014}b"          # any string with a multi-byte UTF-8 char
    val byte_arr = s.bytes()
    val b = byte_arr[0]           # the ASCII 'a' byte, decimal 97
    print "b={b}"                 # prints: b=97  (correct)
    print "b >= 97 -> {b >= 97}"  # true   (correct)
    print "b <= 122 -> {b <= 122}"# FALSE  (WRONG — 97 <= 122 is true)
    val c: i64 = b
    print "c={c}"                 # prints: c=776  (== 97 << 3 — WRONG, should be 97)
    print "int(b)={int(b)}"       # prints: int(b)=97 (correct — int() unboxes properly)
    print "int(b)<=122 -> {int(b) <= 122}"  # true (correct once explicitly cast)
```

`776 = 97 << 3`: the raw boxed/tagged representation of the `u8` (value shifted
left 3 bits, presumably a pointer/NaN-boxing tag scheme) leaks through
relational comparison and explicit `i64` re-annotation, but NOT through
`print` interpolation or the `int(...)` builtin cast (both of which correctly
unbox). Plain arithmetic (`b + 0`) also does *not* fix it — the result still
prints as `97` under interpolation but fails the same `<=` comparison as
`b` itself, i.e. the corrupted tag survives simple arithmetic.

## Impact discovered via

`src/compiler/90.tools/duplicate_check/tokenizer.spl`'s `tokenize()` iterates
`source.bytes()` and classifies each byte via range checks
(`b >= 97 and b <= 122`, `b >= 48 and b <= 57`, etc.) to find identifier/digit
runs. Any `.spl` file containing a multi-byte UTF-8 character *anywhere*
earlier in the file (even fully inside a `#` comment, a string literal, or as
a stray byte — position/context does not matter) causes every subsequent
byte's classification to become unreliable, which desyncs the tokenizer's
scan position for the rest of the file and corrupts all downstream
tokens/keywords. Confirmed this is not a `duplicate_check`-specific bug: the
tokenizer's dispatch logic is correct pure-Simple code; the seed interpreter's
comparison of the boxed `u8` is the actual defect.

**Not a production-path finding**: per repo convention (`bin/release/<triple>/simple`
is the self-hosted default; the seed at `src/compiler_rust/target/release/simple`
is bootstrap-only and known to have `BoxInt` tag artifacts elsewhere — see
`project_stage4_wall_and_hardening_2026-07-04` memory entry, "seed BoxInt <<3
mangles enum heap-handles thru ANY channels; SEED-specific, pure-Simple codegen
CLEAN"). This investigation could only run on the seed (deployed self-hosted
binary is stale / rejects `rt_cli_arg_count`, per current redeploy-wall
status), so this repro is NOT yet confirmed against the pure-Simple self-hosted
compiler. If the self-hosted binary is available, re-run the minimal repro
above against it before prioritizing a seed-side fix.

## Workaround (used in this task, NOT landed as a code change)

Wrap any byte pulled from `.bytes()` in `int(...)` before relational
comparison. Deliberately NOT applied inside
`src/compiler/90.tools/duplicate_check/tokenizer.spl` for this task: the
tokenizer's own logic is correct, the defect is in the seed's comparison
of boxed `u8`, and patching production Simple source to route around a
bootstrap-only interpreter artifact (unverifiable against the real
self-hosted compiler in this session) would be treating the symptom, not
the cause, in a file outside this task's fix scope.

## Next step

Bisect the seed interpreter's relational-operator lowering for `u8`-typed
operands (`src/compiler_rust`) — likely the same `BoxInt` tag-shift family as
the Stage4 wall note. Add a minimal `.spl` regression
(`xs = "a\u{2014}b".bytes(); assert xs[0] <= 122`) once a fix lands, and
re-verify `duplicate-check --mode token` against a fixture containing
non-ASCII comments/docstrings (common in this i18n'd repo) to confirm the
tokenizer needs no changes once the seed defect is fixed.
