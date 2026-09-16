# Seed JIT: the explicit `Some(x)` optional constructor produces a corrupt value

- **Filed:** 2026-09-13
- **Status:** FIXED 2026-09-13 (see "Resolution" at the bottom). Two distinct
  halves: the `Some(x)`-into-`T?` boxing half was already fixed in the Rust
  source (`rt_unwrap_or_self` in `hir/lower/expr/control.rs`) but the DEPLOYED
  Windows artifact `bin/release/x86_64-pc-windows-msvc/simple.exe` (built
  2026-09-01 17:42) predates it; the second half — `str(<unwrap>)` — was still
  live in source and is fixed here.
- **Severity:** high — silently wrong values, no crash, no diagnostic
- **Host:** Windows 11, `bin/release/x86_64-pc-windows-msvc/simple.exe` (Rust bootstrap seed)
- **Affects:** default execution mode (JIT). `SIMPLE_EXECUTION_MODE=interpreter` is correct.

## Symptom

Under the seed's default JIT, a value built with the explicit `Some(...)`
constructor reads back as neither `nil` nor the value it was given. Unwrapping
it yields a text whose `.len()` is `-1`, which compares unequal to every
literal, and which makes `print` emit nothing at all. The implicit optional
coercion (`val c: text? = "hello"`) is unaffected.

## Minimal repro

```simple
fn main():
    val o: text? = Some("hello")
    print("1:[" + o! + "]")
    print("2:" + str(o! == ""))
    print("3:" + str(o! == "hello"))
    val t: text = o!
    print("4:[" + t + "] len=" + str(t.len()))
    print("5 len=" + str(o!.len()))
```

Measured 2026-09-13:

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `1:[hello]` / `2:false` / `3:true` / `4:[hello] len=5` / `5 len=5` — **correct** |
| default / `SIMPLE_EXECUTION_MODE=jit` | line 1 missing entirely, `2:false`, `3:false`, line 4 blank, `5 len=-1` — **wrong** |

`i64?` is affected too (`str(Some(42)!)` prints nothing), and so is the same
value stored in a struct field. A plain coercion is not:

```simple
val c: text? = "hello"      # c! == "hello"  ->  true, even under JIT
val b: text? = Some("hello") # b! == "hello" ->  FALSE under JIT
```

## Impact observed

`storage_root_environment_snapshot()`
(`src/lib/nogc_sync_mut/storage_roots/environment_owner.spl`) builds its fields
with `Some(value)`. Under JIT the `LOCALAPPDATA` field is therefore neither
`nil` nor the path, `_default_user()` in
`src/lib/nogc_sync_mut/storage_roots/resolver.spl` answers `nil`, and
`inspect_storage_roots` returns `Err(StorageRootError.UnsetDefaultUnavailable)`.
Every MCP CLI passthrough tool then answers
`centralized child storage environment is unavailable`.

This is a *different* defect from
`seed_result_err_shorthand_closure_segv_2026-09-12.md`. That SEGV is fixed; the
current failure is a clean `Err`, reached because the optional value is wrong.

## Mitigation in place (not a fix)

`bin/simple_mcp_server.cmd`'s source branch now defaults
`SIMPLE_EXECUTION_MODE=interpreter`, mirroring
`bin/simple_lsp_mcp_server.cmd`. Interpreter mode is also faster to first reply
here (initialize 1.20s vs 3.27s JIT), so this costs nothing on the MCP lane.
`scripts/check/check-mcp-stdio-roundtrip.shs` exports the same default and now
reads `isError`, so a regression is caught: forcing
`SIMPLE_EXECUTION_MODE=jit` makes that gate FAIL with the exact message above.

The mitigation does not cover any other JIT consumer of `Some(...)`, which is
most of the tree. The real fix belongs in the seed's JIT lowering of the
optional constructor.

## Next step

Locate the `Some` constructor lowering in the Cranelift/JIT path of
`src/compiler_rust/` and compare it with the coercion path, which is correct.
Add a regression spec once fixed.

## Resolution (2026-09-13, measured)

**Binary identity.** Repros below were run with the freshly built seed
`src/compiler_rust/target/release/simple.exe`. Do NOT use
`bin/release/x86_64-pc-windows-msvc/simple.exe` for this bug: that artifact is
from 2026-09-01 17:42 and still reproduces the original `text?` symptom
verbatim (`3:false`, `5 len=-1`) — the deployment is stale, not the source.

**Half 1 — `Some(x)` boxing: already fixed in source, deployment stale.**
On a seed built from the current tree, the filed repro answers `1:[hello]`,
`2:false`, `3:true`, `4:[hello] len=5`, `5 len=5` under default JIT. The
`rt_unwrap_or_self` normalizer in `compiler/src/hir/lower/expr/control.rs`
(scalar, class/struct and user-enum pointee branches) is the fix. No further
source change was needed; what is needed is a redeploy of the Windows seed.

**Half 2 — `str(<unwrap>)` produced a corrupt text: fixed here.**
Even on the new binary, `str(m!)` was wrong while `val u: i64 = m!; str(u)`
was right:

```simple
val m: i64? = 42
val s: text = str(m!)     # JIT: s.len() == -1, s == "42" is false
```

Cause: `x!` on a nullable scalar is deliberately typed `TypeId::ANY` (the word
stays a TAGGED RuntimeValue — see the comment in `lower_try`), but
`lower_cast_expr` (`compiler/src/mir/lower/lowering_expr_ops.rs:556`) only
converted for real when the source type was a *native* scalar. For `ANY` it
fell through to `MirInst::Cast`, which codegen emits as a plain value copy, so
the tagged word masqueraded as a STRING pointer — the exact `len == -1` /
`rt_string_concat` -> NIL failure that comment already describes for raw ints.

Fix: route `ANY -> STRING` through `emit_to_string` as well. Its existing
`_ => reg` arm already treats a value that is already a RuntimeValue correctly
and calls `rt_value_to_string`. One-line predicate change; `STRING -> STRING`
and every other target are untouched.

**Verification (all under default JIT, seed rebuilt 2026-09-13 10:13):**

```
$ src/compiler_rust/target/release/simple.exe run some2.spl
1:[hello] / 2:false / 3:true / 4:[hello] len=5 / 5 len=5 / 6:42
$ src/compiler_rust/target/release/simple.exe run i2.spl
len=2 / eq42=true / D:42
```

Regression smoke (`str` on text, f64, bool, array len, struct field, i64::MAX)
is byte-identical between `SIMPLE_EXECUTION_MODE=interpreter` and JIT:
`t:abc:3 / f:1.5 / b:true / a:3 / p:7 / i:9223372036854775807`.

**Remaining follow-up (not this bug):** redeploy
`bin/release/x86_64-pc-windows-msvc/simple.exe` from the rebuilt seed, and
then the interpreter-mode mitigation in `bin/simple_mcp_server.cmd` can be
reconsidered. The mitigation is harmless meanwhile (it is also faster).
