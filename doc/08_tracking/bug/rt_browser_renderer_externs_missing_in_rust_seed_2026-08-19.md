# `rt_browser_renderer_*` externs unimplemented in the Rust seed interpreter

Date: 2026-08-19
Status: FIXED 2026-11-11 (p3-interp11 lane) — the whole family is now
registered in the Rust seed interpreter's extern table. Verified on the fresh
seed 46fe8f6b6def. See the 2026-11-11 addendum at the end.
Found by: `test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl`

## Symptom

```
hosted browser process and pipe performance
  ✗ reuses an unchanged frame after each changed process reply
    semantic: unknown extern function: rt_browser_renderer_spawn_sandboxed
Results: 1 total, 0 passed, 1 failed
```

## Analysis

`src/lib/nogc_sync_mut/io/process_ops.spl:17` declares
`extern fn rt_browser_renderer_spawn_sandboxed(cmd: text, args: [text]) -> i64`.

The symbol IS defined in the C runtime
(`src/runtime/runtime.h:704`, `src/runtime/runtime_process.c:889`) and is
listed in `src/compiler/70.backend/backend/stage4_symbol_closure.spl:622`,
so native builds resolve it.

It is NOT registered anywhere in the Rust seed interpreter --
`grep -rn "rt_browser_renderer" src/compiler_rust/` returns **zero** hits for
the entire `rt_browser_renderer_*` family. The seed interpreter therefore
cannot execute this spec at all.

This is a seed-interpreter capability gap, not a defect in the spec or in the
browser product code. The spec should be run on a native/self-hosted lane, or
the family must be registered in the Rust interpreter's extern table.


## 2026-11-11 — P3 interp11 triage verdict: FIXED (verified on fresh seed 46fe8f6b6def)

The `rt_browser_renderer_*` family is now registered in the Rust seed
interpreter's static extern table: new
`src/compiler_rust/compiler/src/interpreter_extern/browser_renderer.rs` with
all 7 symbols wired into the `insert_simple!` table
(`interpreter_extern/mod.rs:1703-1709`), landed via the 2026-11-07 merge
`9e7e7a526edb` (PR #7597). Seed semantics mirror the C runtime's non-Linux
arms: sandbox unavailable => `spawn_sandboxed` and `write_protocol_some`
return `-1`, the three sandbox-state predicates return `false`, and the
stdin/stdout helpers do real bounded I/O.

Seed-smoke verification (2026-11-11): probe
`build/review/interp11_browser_renderer_probe_spec.spl` (5 examples) passes 5/5
on the seed — every call resolves (the original "unknown extern function:
rt_browser_renderer_*" defect cannot regress) and returns exactly the
documented degraded values, including real bounded stdout writes.

Residual (out of scope, environment limit, unchanged by this row): the full
perf spec `test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl`
still cannot pass end-to-end on a seed because no sandbox exists in the seed
(`start()` gets the refused `-1`); it must run on a native/self-hosted lane
with a real sandbox, exactly as this doc originally concluded.
