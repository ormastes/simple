# Seed MIR: `defer` clobbers a function's implicit-tail return value (JIT SIGSEGV / wrong value)

- **Filed:** 2026-11-06 (found behind the JIT dynlib fix,
  `seed_jit_host_dynlib_open_text_arg_not_split_2026-11-06.md`)
- **Component:** Rust seed MIR lowering (`mir/lower/lowering_core.rs`), so every
  MIR backend (Cranelift JIT, LLVM) is affected
- **Severity:** high: silent wrong return value, or a null struct handle and a SIGSEGV
- **Status:** fixed (branch `work/seed-jit-batch2-20261106`)

## Symptom

```simple
fn run_int() -> i64:
    defer rel()
    val r = 41 + 1
    r            # JIT returned 0 (rel()'s nil, unboxed)
```

With a struct tail the function returned a null handle, and the first field read
crashed (rc 139). In the field this hit `SimpleHttpServer.handle_connection_on_owner_v1`
(`defer self.admission.release()` followed by an `outcome` tail). That made every JIT run of
`test/02_integration/app/vector_provider/http_vector_parser_live_socket.spl`
crash once its provider loaded. The interpreter was correct.

Fixture: `test/fixtures/compiler/seed_jit_miscompiles/defer_implicit_tail_return.spl`
(expected `int=42`, `ok=true reason=handled`; before: JIT printed `rel` then SIGSEGV rc 139).

MIR before the fix (`SIMPLE_DUMP_MIR=1`):

```
Load { dest: VReg(4), ... }                      # tail `r`
Call { dest: Some(VReg(6)), target: Pure("rel") } # deferred
UnboxInt { dest: VReg(7), value: VReg(6) }
terminator: Return(Some(VReg(7)))                 # returns rel()'s value
```

## Root cause

`lower_function` lowered the body and then called `emit_deferred_blocks`. After
that it read `self.last_expr_value` to build the implicit `Return`. Lowering the
deferred statements overwrote `last_expr_value`
(`mir/lower/lowering_core.rs`, `emit_deferred_blocks`). The explicit `return x`
path was unaffected because it captures `ret_reg` before emitting the defers.

## Resolution

`emit_deferred_blocks` saves `last_expr_value` before lowering the deferred
bodies and restores it afterwards.

Rust test `compiler/tests/defer_tail_return_jit.rs::defer_keeps_implicit_tail_return_value`
— before: FAILED (`left: 1` = tail case returned the deferred value); after: ok.

End to end (seed built from this branch, JIT):
fixture prints `rel / int=42 / rel / ok=true reason=handled`. The live socket
probe with `simple_vector_provider_levelled.dll` (sha256 `ff317f5a…1ecc`) prints
`HTTP_VECTOR_LIVE_SOCKET_PROBE_COMPLETE provider_used=true retained_session_reused=true scalar_fallback=true security_rejection=true`
and exits with rc 0.
