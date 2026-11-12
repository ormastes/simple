# `for (i, x) in xs.enumerate()` types `x` as unit in the native lane

- Status: OPEN (workaround at the one known site). Severity P2.
- Found: 2026-11-13, Windows Phase 2 compiler (frozen sha256 `c5c28bb7149f…`,
  pin `19c5aea975e5`) building the Phase 4 MCP server.
- Component: pure-Simple HIR/MIR typing of tuple destructuring over
  `enumerate()`; LLVM emission.

## Symptom

```
llc: module.ll:1585:33: error: void type only allowed for function results
  %l41 = call i64 @rt_native_eq(void %l35, ptr %l40)
```

in `lib.common.debug.service_v1.DebugServiceV1._reclaim_terminal_probe`, from

```simple
for (idx, probe) in self.probes.enumerate():
    if probe.state != DebugProbeStateV1.Applied:
```

The loaded field `probe.state` is emitted with type `void`: the destructured
tuple element `probe` (element type `DebugProbeV1`) is typed as unit, so its
field read and the `!=` operand lose their type. Indexing the same array
(`self.probes[idx].state`, line 451 of the same file) compiles.

## Workaround

`service_v1.spl` `_reclaim_terminal_probe` uses an indexed `while` loop,
linked to this record. Restore the `enumerate()` form when fixed.

## Fix needed

Type the tuple pattern elements of `for (a, b) in xs.enumerate()` from the
element type of `xs` (`(i64, T)`), in HIR, so MIR/LLVM never see a unit-typed
`b`. Add a native regression spec (a field read + enum comparison on `b`).
