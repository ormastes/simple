# Seed JIT: the explicit `Some(x)` optional constructor produces a corrupt value

- **Filed:** 2026-09-13
- **Status:** OPEN
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
