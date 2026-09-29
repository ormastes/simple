# `rt_browser_renderer_*` externs unimplemented in the Rust seed interpreter

Date: 2026-08-19
Status: OPEN (environment/tooling limit)
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
