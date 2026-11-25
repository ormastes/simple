# Native: `"{a() and b()}"` interpolation fails llc (ptr vs i64 type mismatch)
## Resolved 2026-11-25 — source fix verified present; native execution environment-blocked

(Supersedes the 2026-09-16 normalization-pass "needs owner triage" note.)

**Status:** RESOLVED 2026-11-25 (fix verified in source; native-build execution
not runnable on the verifying host — see note below)  **Found:** 2026-07-16 (p_shortcircuit lane)  **Path:** native-build --entry (strict-llvm)
```simple
fn t() -> bool:
    return true
fn main() -> i64:
    print("v={t() and t()}")   # build fails: llc exit 1
    return 0
```

`llc-18: '%lNN' defined with type 'ptr' but expected 'i64' — %t5 = inttoptr i64 %lNN to ptr`

## Notes

- PRE-EXISTING at base de7cb5a238a: reproduces identically with and without the
  p_shortcircuit Bool-result fix for the And/Or lowering (only the local number
  shifts, `%l18` pre / `%l20` post), so it is not caused by that change.
- A logical `and`/`or` result used in a string interpolation slot routes
  through `coerce_concat_operand` (expr_dispatch.spl); some operand along that
  chain ends up `ptr`-typed where the emitter expects `i64`, producing an
  invalid `inttoptr` whose source is already a pointer.
- LOUD failure (build error), not silent-wrong output. Plain `print(a and b)`,
  `if`/`while` conditions, `val` bindings, and nested `and`/`or` all build and
  run correctly with the short-circuit lowering + Bool-result fix.

## Root cause and fix

`ssa_alloca_transform_blocks` renames slotted definitions to fresh locals that
have no `MirLocal` entry. `translate_const` therefore used its native-integer
fallback for the renamed `Const(Str, Opaque("str"))`, leaving the emitted GEP
recorded as `i64` when the generated Store needed `ptr`. Fresh constant locals
now take their type from the Const instruction itself; declared locals retain
their pre-registered type. A focused LLVM regression and strict dual-backend
interpolation case cover the failure. Execution remains pending because this
lane was limited to static/source verification.

## Repro

`env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --entry <case>.spl -o <bin> --clean`


## Verification 2026-11-25 (p2w4-al lane, Windows host)

Code inspection at release/1.0.0 HEAD: the fix described under "Root cause and
fix" is present in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`
(`translate_const`, ~line 2615): fresh SSA-renamed constant locals with no
`MirLocal` entry now take their LLVM type from the Const instruction itself
(`local_types.has(dest_id)` branch at lines 2620-2628), with the comment
explicitly citing the poisoned-pointer-constant mechanism this bug records.
Execution evidence is NOT claimed: `native-build --entry` with llc-18 is not
available on this Windows host, and the pinned seed binary cannot load the
current tree (`unknown decorator '@representation_boundary'` in
`src/app/test_runner_new/test_runner_client.spl`), so no spec run was possible.
Closure rests on source inspection only, as stated.
