# native-build: top-level script `.len()` const-folds to 0 (no `fn main`)

**Severity:** high (silent-wrong)
**Found:** 2026-07-14, exprdispatch2 lane
**Resolved:** 2026-07-15 (triage-confirmed 2026-07-17: `toplevel_array_len` case verified present in `scripts/check/check-native-seed-parity.shs`)
**Backend:** native-build `--entry`

## Symptom

Top-level statements written directly in a `.spl` file with **no enclosing
`fn main():`** silently const-fold array/collection `.len()` (and the whole
construction chain) to `0`.

```simple
val a = [1, 2]
print(a.len())        # native prints 0; oracle prints 2
```

Wrapping the identical code in `fn main() -> i64:` produces the correct result
(verified — this is specifically the top-level-script path).

## Root cause

The Flat AST bridge placed named top-level bindings in module constants while
only bare `_expr_N` declarations entered its synthetic `main`. MIR constant
lowering supports scalar literals only, so the script's array never acquired
the runtime handle and `runtime_array_locals` metadata that ordinary local
array lowering creates. The later bare `print(xs.len())` therefore read a zero
global fallback.

## Resolution

When a file has bare expressions and no explicit `main`, the bridge now replays
its named `val`/`var` bindings in source order inside the synthetic `main`.
Those bindings follow normal local lowering, so array construction and `.len()`
use the canonical runtime metadata path. Module constants remain present for
import semantics; this deliberately does not claim to implement general
heap-backed module initializers, which remain a separate documented backend
gap.

`scripts/check/check-native-seed-parity.shs` now includes the exact no-`main`
case and reports `toplevel_array_len ... PASS` in the 39-case gate.

## Reproduce

`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry t.spl -o out --clean`
with a brace-less top-level `[..]; .len()`; compare to `bin/simple run t.spl`.
