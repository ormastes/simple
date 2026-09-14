# Seed JIT: the explicit `Some(x)` optional constructor produces a corrupt value

- **Filed:** 2026-09-13
- **Status:** PARTIALLY FIXED (pending seed redeploy AND full re-verification)
  — see "Root cause and fix" below. One confirmed contributing defect is fixed:
  `str(x)`/`text(x)` where `x` is an ANY-typed force-unwrap (e.g.
  `str(Some(42)!)`, or any `str(y!)` on a nullable scalar) was silently
  corrupted by `lower_cast_expr` falling through to a bare `MirInst::Cast`
  instead of a real to-string conversion. This is verified **only at the MIR
  level** (a lowering-stage regression test), not by rebuilding the seed and
  re-running the repro table below — that re-run is still outstanding.
  It does **not** explain the full repro: none of the repro's 5 print lines
  actually calls `str()`/`text()` directly on the unwrapped value (line 1 and
  4 are string concatenation, `+`; line 3 is `==`; line 5 is `str(o!.len())`,
  where `.len()` on an already-corrupt word is what produces -1, not the
  `str()` call itself). It also does not explain the reported asymmetry
  between `Some(x)` (broken under JIT) and plain coercion `val c: text? = x`
  (fine under JIT) — `x!`'s HIR type is `ANY` in both cases per `lower_try`,
  so this fix is symmetric between them, meaning a **second, still-open**
  defect likely lives in the `Some(...)` constructor's lowering itself, not in
  `lower_cast_expr`. Re-run the full repro table on a redeployed seed before
  closing this record.
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

## Root cause and fix

`x!` (force-unwrap, `Expr::ForceUnwrap`) on a nullable scalar (`i64?`, `text?`,
...) lowers via `lower_try` (`src/compiler_rust/compiler/src/hir/lower/expr/control.rs`),
which deliberately types the result `ANY` — the runtime word is still a tagged
`RuntimeValue`, not the raw scalar (see the comment there, and
`jit_optional_i64_payload_reinterpreted_2026-08-17.md`).

`str(x!)` / `text(x!)` then lowers through `lower_cast_expr`
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs:549`), which
special-cases only `is_native_scalar(inner.ty)` sources for a real
to-STRING conversion (`emit_to_string` -> `rt_value_to_string`); anything else
falls through to a plain `MirInst::Cast`, a value-copy in codegen. An
`ANY`-typed source is *not* a native scalar (it's a tagged word), so it fell
through to the plain copy, which is exactly the "reinterprets a tagged
RuntimeValue as a raw STRING pointer" corruption described in the comment
directly above that `if` (`rt_string_concat` then reads a corrupted length
and returns NIL). This exact `str(y!)` / `text(y!)` shape is confirmed
corrupted independent of the specific repro table above (which exercises `+`
concatenation and `.len()` on the unwrapped value, not a direct `str()`/`text()`
call — see the Status note).

Fix: also route `ANY`-typed sources through `emit_to_string`:

```rust
if target == TypeId::STRING && (Self::is_native_scalar(inner.ty) || inner.ty == TypeId::ANY) {
    return self.emit_to_string(source_reg, inner.ty);
}
```

`emit_to_string`'s existing `_ => reg` default (heap/tagged values are already
`RuntimeValue`s) then calls `rt_value_to_string` directly on the ANY word,
which is correct since `x!`'s ANY-typed result already *is* a tagged
`RuntimeValue`.

Regression test (MIR-lowering level, asserts the emitted MIR calls
`rt_value_to_string` and contains no `MirInst::Cast { to_ty: STRING, .. }`):
`src/compiler_rust/compiler/src/mir/lower/tests/seed_regression_tests.rs`,
`str_of_force_unwrapped_nullable_scalar_routes_through_to_string`. Verified to
fail without the fix and pass with it.

Landed via PR (branch `work/seed-str-unwrap-any`); the fix ships to users once
the seed binary is next redeployed from this source.

## Next step

1. Rebuild the seed with this fix and re-run the full repro table above
   end-to-end under default JIT. This PR verified the fix only at the MIR
   level (a lowering-stage unit test), not by executing a rebuilt binary
   against the repro.
2. `x!` types `ANY` for both `Some(x)` and plain coercion (`val c: text? = x`),
   so this fix is symmetric between them and does not by itself explain why
   coercion already worked under JIT while `Some(...)` didn't. That points at
   a second, separate defect in the `Some(...)` constructor's own lowering —
   locate it in the Cranelift/JIT path of `src/compiler_rust/` and compare it
   with the coercion path.
3. Re-verify the `==`-comparison symptom (line 3 of the repro table) — it goes
   through `BinOp::Eq` lowering for `ANY` operands, not `lower_cast_expr`, and
   was not touched by this fix.

Do not close this record until step 1 confirms the full original repro is
clean on a redeployed seed.
