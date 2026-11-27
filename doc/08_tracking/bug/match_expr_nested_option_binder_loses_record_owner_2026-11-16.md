# Match-expression value bound by `Ok(Some(v))` loses its record owner (field reads hit field 0)

- Found: 2026-11-16, Stage 3 self-build (r16, llvm backend):
  `unsupported LLVM value conversion from i64 to void
  function=...FileFiberTldrBridgeV1._drain_completions value=%l98`
  (`src/compiler/80.driver/driver_build/file_fiber_tldr_bridge_v1.spl:329`).
- Status: open (MIR source). Stage 3 lane workaround on
  `work/stage3-payload-const-wa-20261116`.

## Minimal shape

```
val taken: Result<S?, E> = take()
val c = match taken:
    case Err(_): return -1
    case Ok(Some(value)): value
    case Ok(_): return -2
c.second_field
```

`c` is typed as an untyped I64 and has no record owner. Every field read
resolves to field 0, and on the release source (seed-interpreted MIR dump)
the GetField destination type is `Unit`. Natively:

| producer | result |
|---|---|
| seed interpreter | correct |
| integ2 Stage 2, cranelift | builds; the run reads field 0 (silent wrong value) |
| r16 Stage 3, llvm | `i64 -> void` conversion compile error when the field is compared with a u64 |

Arm order does not matter. A `: S` annotation on `c` removes the llvm error
but still reads field 0. Single-level `Ok(value)` on `Result<S, E>` is
correct, and so is an `if val r = opt: r` then-arm.

## Cause (located, not fixed)

`emit_enum_payload_deep` is called for a nested `Option` sub-pattern with an
empty owner and variant
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, the Option
arm of the deep-pattern lowering, `"rt_unwrap_or_self", ..., "", ""`). The
inner binder therefore gets no declared type and no struct identity from the
outer `Result<S?, E>` Ok payload. The fix needs the outer variant's declared
payload type (`S?` -> `S`) passed down to that call.

## Workaround

Fill the optional first, then bind with the then-arm of `if val`:

```
if not self.pending.?:
    match taken:
        case Ok(Some(value)): self.pending = Some(value)
        ...
val c = if val retained = self.pending:
    retained
else:
    return Ok(())
```

Fixtures: `build/voidfx/void_variants{,2,3}.spl` in the lane worktree, run
via `native-build <file> --backend cranelift|llvm`.
