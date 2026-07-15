# native-build: top-level script `.len()` const-folds to 0 (no `fn main`)

**Severity:** high (silent-wrong)
**Found:** 2026-07-14, exprdispatch2 lane
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

## Root cause (suspected)

`SIMPLE_KEEP_LLVM_IR=1` shows the entire array-construction + `.len()` chain
replaced by a bare `add i64 0, 0` (const zero). Likely in the top-level/module
statement lowering (candidate: `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`,
which a parallel lane also touches) — the synthetic top-level body drops the
runtime-array local tracking that `fn`-bodies get, so `.len()` sees a non-runtime
local and folds.

## Fix direction

Ensure top-level/module-statement lowering tags runtime-collection locals the
same way function-body lowering does, so `.len()`/indexing route to the runtime
helpers instead of const-folding. Until fixed, `--entry` programs should either
require a `fn main` or loud-fail on un-tracked collection ops at top level —
never silently emit 0.

## Reproduce

`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry t.spl -o out --clean`
with a brace-less top-level `[..]; .len()`; compare to `bin/simple run t.spl`.
