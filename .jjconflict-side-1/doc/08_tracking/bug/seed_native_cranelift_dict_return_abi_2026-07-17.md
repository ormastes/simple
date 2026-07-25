# Seed native cranelift miscompiles a function that RETURNS a `Dict` by value

**Date:** 2026-07-17
**Lane:** S57 (found while disproving the `{}` land-war; filed, not fixed here)
**Severity:** P2 (silent wrong result / garbage handle, no crash) on the seed's
`--native --backend=cranelift` path only
**Status:** OPEN — reproduced and characterized, NOT root-caused to a line, NOT
fixed (orthogonal to lane S57's assigned `{}` mission; risky cranelift codegen
change; belongs to a codegen lane with its own gates).

## Symptom

On the from-scratch seed's native cranelift path, a function whose return type
is `Dict<...>` hands back a **malformed dict handle**: `len()` reads `-1`,
`contains_key` is `false`, indexing returns garbage, iteration yields 0. The
tree-walking interpreter, `SIMPLE_BOOTSTRAP=1`, and the same code with the dict
kept LOCAL (never returned) are all correct. Returning a **list** (`[i64]`)
from a function is fine — the defect is specific to `Dict` return values.

Independent of empty-vs-non-empty (a non-empty returned dict is equally
broken) and independent of `{}`-vs-any construction — so this is **not** the
`{}` bug and **not** fixable by respelling `{}`→`Map.new()`.

## Reproduction (`src/compiler_rust/`, seed = `./target/bootstrap/simple`)

`scratch_probe_ret2.spl`:

```simple
fn ret_built() -> Dict<text, i64>:
    var d: Dict<text, i64> = {}
    d["a"] = 11
    d["b"] = 22
    d

fn ret_list() -> [i64]:
    val xs = [1, 2, 3]
    xs

fn main() -> i64:
    val d = ret_built()
    print "LEN={d.len()}"
    print "HAS_A={d.contains_key(\"a\")}"
    print "A={d[\"a\"]}"
    var seen = 0
    for k in d.keys():
        seen = seen + 1
    print "ITER={seen}"
    val xs = ret_list()
    print "LIST_LEN={xs.len()}"
    0
```

| path                                             | LEN | HAS_A | A  | ITER | LIST_LEN |
|--------------------------------------------------|-----|-------|----|------|----------|
| interpreter (`seed probe.spl`)                   | 2   | true  | 11 | 2    | 3        |
| `--native --backend=cranelift` (opt=aggressive)  | -1  | false | 3  | 0    | 3        |
| `--native --backend=cranelift --opt-level none`  | -1  | false | 3  | 0    | 3        |

Persists at `--opt-level none`, so it is an ABI/lowering defect, not an
optimizer miscompile. (The `compile`→`.smf` bytecode-VM path aborted with
`rc=129` on the earlier return probe `scratch_probe_ret.spl` — a possibly
related VM defect on function-returned dicts, not chased here.)

`scratch_probe_ret.spl` further isolates the trigger:

| case                                            | native cranelift | interpreter |
|-------------------------------------------------|------------------|-------------|
| P1 return empty `{}` dict, `.len()`             | -1               | 0           |
| P2 return NON-empty dict, `.len()`              | -1               | 1           |
| P3 local `{}` dict never returned, `.len()`     | 0                | 0           |
| P4 dict passed as arg + returned (passthrough)  | 0                | 0           |
| P5 return empty then insert, `.len()`           | -1               | 1           |

Trigger = "the `Dict` value crosses a function return boundary". Local dicts
(P3) and dicts passed *into* a function as arguments (P4) are fine.

## Likely area & blast radius (NOT scoped here)

Almost certainly in the seed's native cranelift return-value handling for
heap/boxed aggregate types in `src/compiler_rust/compiler/src/codegen/` (the
`Dict` return value is likely returned/boxed differently from a `List`, which
works). Any pure-Simple compiler source file that returns a `Dict` by value
could be corrupted if that file is compiled by the **seed's native cranelift**
path during a from-scratch native Stage4 bootstrap. The three guarded frontend
files (`module_assembly.spl`, `convert_nodes.spl`, `desugar_async.spl`) do NOT
return bare `Dict`s (verified: no `-> Dict`/`-> Map` signatures; they build
locally and pass to `parser_module_new(...)`), so they are unaffected.

## Recommended next step

A codegen lane should root-cause in `src/compiler_rust/compiler/src/codegen/`
(compare `Dict` vs `List` return lowering), add a targeted
`cargo test -p simple-compiler --lib` case, and re-run
`scripts/check/native-smoke-matrix.shs`. Out of scope for lane S57.

## Related

- `seed_stage4_empty_dict_literal_2026-07-17.md` — the `{}` land-war
  resolution this was found alongside.
