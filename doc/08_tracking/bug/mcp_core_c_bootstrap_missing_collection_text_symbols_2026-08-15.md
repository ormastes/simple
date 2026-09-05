# MCP core-C bootstrap archive misses collection/text symbols

## Status

Fixed in the frozen worktree. Rust-seed evidence remains diagnostic only.

## Exact reproducer

In `/mnt/data/worktrees/stage4-debug-frozen`, the isolated command used
`SIMPLE_NATIVE_BUILD_RUST=1`, `SIMPLE_NO_STUB_FALLBACK=1`, cache
`build/mini_cache_mcp2`, all three source roots, entry closure
`src/app/mcp/main.spl`, and output
`build/mini_builds/phase4_tools_rust_seed/fresh/simple_mcp_server`.

It compiled 63 cached objects, then failed at link after 16.51 seconds with
329,140 KiB peak RSS. The generated
`build/native-objects-xtMHYq/core_c_runtime/libsimple_runtime.a` lacks:

- `rt_array_enumerate`
- `rt_collection_remove`
- `text_dot_from_char_code`

The unresolved references are from `debug.service_v1` and `json.parser`.
The APIs are valid: their pure-Simple definitions exist in
`src/runtime/simple_core/core_array_query.spl` and `core_string.spl`, Rust
runtime definitions exist, and the admitted Stage-2 runtime archive exports all
three. The defect is therefore the selected/generated `core-c-bootstrap`
runtime archive boundary, not MCP tool source.

## Focused gate

```sh
sh scripts/check/check-mcp-core-runtime-link-symbols.shs \
  build/native-objects-xtMHYq/core_c_runtime/libsimple_runtime.a
```

The gate must pass on the runtime archive selected for MCP before retrying the
failed isolated shard. Do not rewrite debug/JSON callers or enable stub/hosted
fallbacks. After a runtime owner supplies the symbols, rerun the failed shard
once with the existing `build/mini_cache_mcp2`; then run produced `--help` and
`--version` once each.

## Fix and bounded retry

`src/runtime/runtime_native.c` now provides the three exact core-C ABI exports:
Unicode-scalar conversion paired with the Rust/pure-Simple NIL contract,
tuple-producing array enumeration, and receiver-dispatched collection removal
that returns the removed element/value. `src/runtime/runtime.h` declares the
same three symbols; no hosted or stub fallback was added.

The existing `rt_dict_remove` ABI remains the declared `i8` success result.
The new value-returning generic collection path uses a private dictionary-take
helper, avoiding an incompatible return-type change for existing callers.
Clang's full-file syntax check passes, and the native-binary symbol gate's five
fail-closed selftest fixtures pass.

The existing `build/mini_cache_mcp2` retry passed with 1 compiled, 62 cached,
0 failed, 19.02 seconds wall time, and 218,996 KiB peak RSS. The 742 KiB MCP
binary defines all three symbols; the focused symbol gate passed on that final
linked artifact. Its single `--help` and `--version` smokes both exited 0, with
version `Simple MCP Server v4.0.0`.

Provider token usage and comparable completed-bug average: unavailable.
