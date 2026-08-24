# Importing `std.io_runtime` breaks `native-build` — `method 'len' not found on type 'i64'` (2026-08-24)

- **Status:** OPEN
- **Severity:** HIGH — blocks building the MCP server locally, and any app that
  touches `std.io_runtime`
- **Area:** seed interpreter extern dispatch + the
  `std.io_runtime` <-> `io/process_ops` <-> `io/process_governor` import cycle
- **Found by:** attempting a local MCP build through the interpreted pure-Simple
  compiler

## Four-line reproducer

```
use std.io_runtime.{env_get}

fn main() -> i64:
    print("ok")
    return 0
```

```
cd src/compiler_rust && cargo build --release --bin simple     # 2m08s, current seed
target/release/simple run src/app/cli/bootstrap_main.spl native-build repro.spl -o /tmp/out
-> error: semantic: method `len` not found on type `i64` (receiver value: 38)
-> rc=1, no binary produced
```

`env_get` is never called. **The import alone is sufficient.**

## Isolation (each row measured, cold cache, same worktree and seed)

| fixture | result |
|---|---|
| no imports at all, `print("ok")` | **builds, rc=0** |
| `use std.nogc_sync_mut.io.stderr_ops.{stderr_write}` | **builds, rc=0** |
| `use std.io_runtime.{env_get}` | FAILS, receiver value 38 |
| `use std.io_runtime.{env_get, file_exists, exit, get_args}` | FAILS, receiver value 38 |
| `use std.nogc_sync_mut.io.process_ops.{process_run_bounded}` | FAILS, receiver value **254** |
| `use std.nogc_sync_mut.io.process_governor.{proc_slot_acquire}` | FAILS, receiver value 38 |
| `src/app/mcp/main.spl` (the real target) | FAILS, receiver value 38, at parse 11/61 |

**The receiver value is not stable** (38 vs 254 for different entry imports), so
it is a corrupted handle, not user data — the same reading the
`seed_flat_registry_len_i64_2026-07-17` comments in
`interpreter_extern/sffi_string.rs:281` and `interpreter_extern/mod.rs:3255`
give for this message shape.

## What it is NOT

- **Not caused by the dict keys/values HIR typing** (`fb7e76c489a` /
  `c9da626ec1c`). Control: reverting `expression_core.spl` to the pre-fix
  content in the same worktree, cold cache, reproduces the failure IDENTICALLY.
- **Not a plain extern-registry gap of the obvious kind.**
  `scripts/check/check-interpreter-extern-registry-gap.shs` reports
  `PASS — 282 symbol(s) checked, 0 new, 0 stale`, and all four array-returning
  externs declared in `io_runtime.spl` (`rt_file_read_bytes`, `sys_get_args`,
  `rt_dir_list`, `rt_dir_walk`) DO have `insert_simple!` handlers in
  `interpreter_extern/mod.rs` (lines 1366, 2436, 1203, 1206).
- **Not the same manifestation as
  `mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17.md`** (OPEN, P2), though
  it is the same family and that record should be read alongside this one. That
  one fires at RUNTIME of an already-built MCP server, inside
  `_mcp_extract_id()`, with a pointer-shaped receiver (4059709571969), and was
  last re-verified by SOURCE INSPECTION. This one fires at BUILD time, from a
  four-line file with no MCP in it, with small receiver values, and is verified
  by EXECUTION. It blocks strictly earlier: there is no binary to run.

## Lead worth pulling first: a module cycle

`std.io_runtime` imports `std.nogc_sync_mut.io.process_ops`
(`io_runtime.spl:13`), and `process_ops` imports `std.io_runtime` right back
(`process_ops.spl:13,41,42,43,44`), as does `process_governor`
(`process_governor.spl:11,12`). Every fixture that fails pulls this cycle in;
the two that build (`stderr_ops`, no-imports) do not. Whether the cycle is the
cause or merely correlates with the real culprit is NOT established here.

Second lead: `process_ops.spl:10,12` declare TUPLE-returning externs
(`rt_process_run(...) -> (text, text, i64)`), a shape with its own history of
payload-extraction defects.

## Impact

`bin/simple_mcp_server` cannot be built locally through the interpreted lane
today. A fresh seed CAN otherwise run the pure-Simple compiler end to end —
hello world and dict fixtures compile, link, and run — so this single defect,
not the Stage 2 blocker, is what stands between this host and a locally built
MCP server.

## NOT verified

- The exact extern or compiler site that produces the bad receiver was not
  identified. The `.len()` is called inside pure-Simple compiler code while the
  seed interprets it; no source location is printed with the diagnostic.
- The cycle hypothesis is a lead, not a diagnosis — no experiment was run that
  breaks the cycle and shows the failure disappearing.
- Nothing was fixed. This record exists so the next lane starts from a four-line
  reproducer instead of a 61-module MCP build.
