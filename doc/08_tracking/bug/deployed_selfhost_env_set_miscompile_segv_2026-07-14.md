# Deployed self-hosted `bin/simple` links a stale `rt_env_set` ABI

The deployed full pure-Simple CLI crashes before parsing `check` input and
before `native-build` reaches user code. The defect is an artifact/runtime ABI
mismatch, not a dropped Simple call argument.

## Symptom

Both a tiny `check` and `native-build` reach glibc `setenv` with a small integer
as its value pointer and exit 139.

## Root cause

The tracked full CLI artifact at
`release/x86_64-unknown-linux-gnu/simple` is SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`
(Build ID `545d912c...`). Its caller correctly expands both `text` arguments to
the current four-register ABI:

```text
rt_env_set(key_ptr, key_len, value_ptr, value_len)
```

Disassembly of the linked `rt_env_set`, however, shows the obsolete two-argument
implementation. It forwards `%rsi` directly as the second `setenv` argument.
For `SIMPLE_BOOTSTRAP_EXPR_COUNT`, `%rsi` is the key length, 27 (`0x1b`), so
glibc calls `strlen(0x1b)` and faults:

```text
__strlen_avx2
  <- __add_to_environ(name="SIMPLE_BOOTSTRAP_EXPR_COUNT", value=0x1b)
  <- rt_env_set
  <- frontend__core___AstExpr__nodes__expr_count_set
  <- frontend__core___Ast__module_state__ast_reset
  <- cli__check___check_path
```

Current `src/runtime/runtime_native.c`, `src/runtime/runtime.h`, and the current
Rust bootstrap runtime all use the correct four-argument ABI. Do not patch
`expr_count_set`, `env_set`, or font code around this stale deployed artifact.

## Rebuild findings

A 2026-07-14 cache-isolated rebuild from current pure-Simple sources established
two later, separate blockers:

1. Stage 2 rejected `src/compiler/50.mir/mir_instructions.spl:588` while using
   the older bootstrap parser (`unexpected token in class body`).
2. Direct Stage 4 reached the linker, then failed because the corrected full-CLI
   closure and selected runtime archive disagreed on both optional integrations
   (SQLite, HTTP, ROCm, oneAPI, OpenGL, SDL2, memtrack, and Cranelift SFFI) and
   core/generated symbols (`rt_file_create_excl`, `rt_file_sync`,
   `rt_crc32_text`, `rt_write_u32s_to_raw`, DirectX constant conversion, and
   `DoubleEndedIterator.rfind`).

The existing focused `src/app/cli/test_entry.spl` shard was also attempted once
with an isolated cache. It remained at one full CPU for 20 minutes after
emitting advisory diagnostics, produced no object/cache artifact, and was
stopped by the session budget guard. Its retained log is a local build artifact,
not release evidence.

Static dependency review then found that the supposedly lightweight entry
imported the full command hub through `run_commands`. It now imports the
zero-import `std.nogc_sync_mut.sffi.cli` owner directly; `run_commands` also no
longer imports its own re-export hub. This source fix has bounded static review
and regression coverage, but still requires native self-host build/execution
proof after the rebuild blockers above are repaired.

## Required fix and gate

Rebuild the bootstrap parser/runtime from current sources, make the full CLI
entry closure and selected runtime bundle agree on their reachable SFFI surface,
then build and deploy one full pure-Simple CLI. Before replacement, the
candidate must pass:

1. disassembly or an executable probe proving four-argument `rt_env_set`;
2. `check` on the tiny existing `p2_add.spl` redeploy fixture;
3. `scripts/check/cert/redeploy_gate/redeploy_gate.shs`;
4. the normal deployed `test` and `native-build` smoke gates.

The Rust seed remains bootstrap-only and is not verification evidence.
