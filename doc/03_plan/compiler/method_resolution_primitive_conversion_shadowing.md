# Plan: fix `u8.to_i64()` mis-dispatch to a same-named user-class method

## Confirmed bug (asm-proven; `x64_freestanding_push_byte_reassign_byte_packed.md`)

On the freestanding OS build, `_u8_at(data,i).to_i64()` (a `u8` chained into
`.to_i64()`) compiled to a call of `services.vfs.vfs_boot_init.VfsFileSize.to_i64`
(`me fn to_i64() -> i64: self.bytes`) — reading a field off the tiny byte value →
`0x53` garbage. `.push(_u8_at(data,i))` avoids it (no `.to_i64()`). A fast repro:
a `class` with `me fn to_i64() -> i64: self.bytes` in the closure + a CHAINED
`u8at(d,i).to_i64()` prints garbage, while a BOUND `val b: u8 = …; b.to_i64()`
prints the correct byte. (Repro entry/harness were throwaway; recipe below.)

## Root of the bug (traced)

- `x.to_i64()` lowers to `HirExprKind.MethodCall(..., Unresolved)`
  (`20.hir/hir_lowering/expressions.spl:395-408`). It is NOT converted to a cast
  by name (no `to_`-prefix handling exists; `primitive_cast_type_kind` only
  handles the `iN(x)` CALL form at `expressions.spl:210-225`).
- Resolution runs in `35.semantics/resolve_strategies.spl:resolve_method:18`:
  instance (`:145` `try_instance_method`) → trait (`:160`) → UFCS (`:242`).
- BOUND `b.to_i64()` (typed `u8`): resolves via `try_instance_method` — the
  builtin int type symbol carries the primitive `to_i64` conversion. Correct.
- CHAINED `u8at(d,i).to_i64()`: the receiver `.type_` is `Infer` (the
  call→method chain does NOT propagate `u8at`'s declared `u8` return — the
  documented "chained methods on erased receivers" limitation). So
  `try_instance_method`/`try_trait_method` return nil and it reaches UFCS.
  `try_ufcs:249` `lookup_function("to_i64")` returns a user-class `to_i64`
  (name-keyed, last-defined-wins), and `:272` `is_compatible(Infer, ClassSelf)`
  returns TRUE via the `(Infer,_) -> true` wildcard (`35.semantics/resolve.spl:83-84`).
  → `FreeFunction(user to_i64)` → MIR emits the wrong call.

## Fix (two coordinated changes)

### A. Root — propagate the call-result type through the chain
Where a `MethodCall` receiver is itself a `Call`/`MethodCall` with a KNOWN
declared return type, set the receiver `HirExpr.type_` to that return type before
`resolve_method` runs, so `u8at(d,i)` carries `u8` and the chained `.to_i64()`
resolves via `try_instance_method` (same as the bound path). Locate the type
inference for Call results (HIR type-check) and ensure a callee with a resolved
signature stamps the call expr's `.type_`. This is the general fix and also cures
other erased-receiver chains — verify it does not shift dispatch for legitimate
chains.

### B. Pragmatic guard — don't let a conversion name UFCS-bind on an Infer receiver
In `try_ufcs` (or `resolve_method` before UFCS): if `method` is a numeric
conversion name (`to_i8/i16/i32/i64/u8/u16/u32/u64/f32/f64` — reuse
`primitive_cast_type_kind` on the `to_`-stripped suffix) AND the receiver type is
`Infer`/unresolved (NOT a concrete user class), do NOT bind to a user-class
method; instead resolve as the primitive numeric conversion (cast) so the value
is correct. MUST NOT fire for a concrete user-class receiver (so
`someClass.to_i64()` still calls the method). This is belt-and-braces for any
residual erased-receiver case A misses, and it converts a would-be `const-0`
(from merely rejecting the UFCS match) into the correct cast.

## Verification bar (do NOT land on probe-green)

1. Fast repro: chained `u8at(d,i).to_i64()` == the byte (65/83) AND a user
   `FileSizeLike.to_i64()` == its field (4242). Both must hold — chained wrong =
   not fixed; class wrong = over-reached.
2. `bin/simple build bootstrap` (3-stage self-compile) — the compiler uses
   `byte.to_i64()`/UFCS on itself; this catches self-compilation breakage.
3. `bin/simple test` — catches the many legitimate user `to_i64` methods.
Land only if all three are green. A parallel session's next bootstrap will eat a
silently-broken resolver change, so the bootstrap gate is mandatory.

## Fix A — IMPLEMENTED (reverted from WC, unverified; bootstrap blocked)

Applied to `src/compiler/35.semantics/resolve.spl` then reverted because the
verification gate could not run (see blocker below). Re-apply exactly:

1. In `resolve_expr`, the `case Call(callee, args, type_args):` arm — after
   `resolved_args`, before building `HirExprKind.Call(...)`, insert:
```
                if not resolved_type.?:
                    val callee_ret = self.callee_return_type(resolved_callee)
                    if callee_ret.?:
                        resolved_type = callee_ret
```
2. Add this method (next to `resolve_call_result_type`):
```
    me callee_return_type(callee: HirExpr) -> HirType?:
        match callee.kind:
            case Var(sym):
                if self.module_functions.contains_key(sym):
                    Some(self.module_functions[sym].return_type)
                else:
                    nil
            case _:
                nil
```
`HirFunction.return_type` is a non-optional `HirType` (`hir_definitions.spl:27`);
`module_functions` is used (not `self.symbols`, which is empty in the resolve
pass — same as `fill_call_defaults`). Guard on `not resolved_type.?` so it only
ADDS a type where inference left none — never overrides (safe for generics).
NOTE: if the chained receiver's type is `Some(Infer)` rather than nil, extend the
guard to also match an `Infer` kind, then re-verify; and add Fix B as the guard.

## BLOCKER: bootstrap gate currently broken (pre-existing, not this change)

`bin/simple build bootstrap` Stage 1 (seed compiles the compiler source) FAILS
with `error: semantic: unknown extern function: rt_lexer_source_set` — an extern
used in `10.frontend/core/lexer.spl`/`parser.spl` that the current Rust seed
(`src/compiler_rust/target/release/simple`) does not provide. The source moved
ahead of the seed (parallel-session drift). Until the Rust seed is rebuilt
(`cargo build --release` in `src/compiler_rust`, coordinated so as not to race a
parallel bootstrap), Fix A/B cannot be verified via the mandatory gate and MUST
NOT be landed. This blocker is independent of the method-resolution fix.

## Repro recipe (throwaway probe)

Freestanding entry with `class FileSizeLike: bytes: i64 / me fn to_i64: self.bytes`,
`fn u8at(d,i) -> u8: rt_bytes_u8_at(d, i.to_i64()).to_u8()`, then compare
`u8at(d,0).to_i64()` (chained) vs `val b: u8 = u8at(d,0); b.to_i64()` (bound),
built `--backend cranelift --target x86_64-unknown-none` and booted in QEMU
(serial print). Chained garbage = bug present.
