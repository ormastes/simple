# Result.map rejects declared record payloads

Status: OPEN — source candidate and regressions AUTHORED_UNEXECUTED.

## Evidence and current-source duplicate check

The actual MCP failure receipt is `/mnt/c/Temp/simple-manual-lanes-20261011/p2-mcp-sosix-stdio/mir-failures.json`: 141 HIR modules passed, then `storage_roots/resolver.spl:177` reported unresolved `map` on `inspect_storage_roots(input).map(_.roots)`. That executable is an older compiler. This candidate does not claim its original diagnostic proves execution of the current-source guard.

Current release inspected: `7de247f6bcfa0f3143742f801ba120f20915db38`. `method_calls_literals.spl` and `builtin_method_extras.spl` are unchanged since d4dd079c. Result combinator dispatch exists in this source, but `builtin_result_payload_mir` admits only i64/f64/bool/text. Both `StorageRootResolution` input and `StorageRoots` output are declared records, so the current lowering still cannot admit the required operation. The nearby JSON `array_ops.spl:479` blocker remains separate: `json_to_array` returns `any?`, and the inferred nested local reaches MIR as Tuple. No tuple-as-array coercion is introduced.

## Narrow repair and contracts

Only `Result.map` and `map_err` gain declared Struct/Class record payloads. Owner lookup mirrors `Result.unwrap`: Struct name and canonical Class identity. Payload extraction remains `rt_enum_payload` into an unchanged i64 word, with the declared HIR type and field-owner metadata preserved for inline callback parameter field reads. Mapper output requires both declared record HIR and the established i64 carrier; unknown `any`, tuple, enum, inference or unsupported primitive forms retain rejection. Existing primitive inference and validation remain the fallback. Result.ok and Option.map admission are unchanged.

The existing discriminant split still invokes the mapper only on its selected branch. Other variants forward the original Result handle, retaining the untouched payload/error layout. The selected branch uses the existing rt_enum_new constructor and float-bitcast path. No runtime allocator, free, global ownership, backend ABI, or generic pointer unwrapping changes occur. The additional work is bounded nominal-symbol lookup and local provenance registration; no latency/RSS improvement or native memory qualification is claimed.

## Regression and qualification boundary

The existing real frontend → HIR → MIR suite gains nested record shorthand projection, record-to-primitive, record error mapping, unchanged primitive mapping, and input/output tuple rejection cases. These assert diagnostics plus concrete Result runtime calls/branch labels. The standalone native entry checks full field values, Ok mapper count exactly one, Err mapper count zero, corresponding map_err behavior, and primitive output. Expected stdout is `Result record map: PASS\n`, exit 0; no stubs or Rust seed fallback permitted.

All new tests are UNEXECUTED: no newly admitted test owner is available, and exhausted historical producer/aggregate cycles were not restarted. Required compiler/lib/MCP/LSP checks and smoke gates remain pending. First qualify a source-containing producer with actual Hello, then execute the real MIR suite and the standalone native entry with its admitted runtime/backfill. This repair does not alone qualify the full MCP closure or resolve missing receiver type provenance on another producer.
