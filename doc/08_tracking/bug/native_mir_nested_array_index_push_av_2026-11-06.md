# native_mir_nested_array_index_push_av_2026-11-06

- Severity: P1, status: open
- Found while splitting the repro for mutate_through_index_loses_write_2026-07-31.

## Repro
`test/fixtures/compiler/mutate_index_nested_array_push/main.spl`:

```
var grid: [[i64]] = [[], []]
grid[1].push(7)
```

The native build uses `s3_fable46_w5` (a copy of `C:/dev/p3new/s3new/s3_fable46.exe`) with the `s3sanity/run_case.ps1` recipe at CapGB 4. The compiler exits with rc=-1073741819 (0xC0000005) at `mir_lower:first_module`, and no objects are emitted. The interpreter (`bin/simple.exe run`) passes.

## Suspect
The mutating-method write-back pre-lowering for an `Index` receiver whose element type is itself an array is in `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (wb_kind 1, ~line 4369).
