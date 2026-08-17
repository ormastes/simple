# engine2d JIT timing probe blocked by `rt_file_is_char_device` unresolved symbol (2026-08-08)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Summary

A genuine Cranelift-JIT-vs-interpreter timing baseline for the engine2d SIMD
kernels (`render_2d_vulkan_functional_coverage_plan_2026-08-07.md` unit B2)
could not be obtained on the deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`). Any module that calls
`std.nogc_sync_mut.io_runtime.time_now_unix_micros` — the standard timing
primitive, needed to measure anything at all — silently drops the WHOLE
module to the tree-walk interpreter under `bin/simple run`, independent of
`SIMPLE_EXECUTION_MODE`.

## Evidence

```
$ bin/simple run /tmp/mini_probe.spl
...
[jit-fallback] unresolved external symbol 'rt_file_is_char_device': whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile: Module error: unresolved external symbol 'rt_file_is_char_device' would NULL-jump in JIT; deferring to interpreter
scalar_us=351 simd_us=445
```

Minimal reproduction (`mini_probe.spl`):

```
use common.gpu.engine2d.scalar_oracle.{oracle_fill_const, oracle_hash_span}
use std.nogc_sync_mut.gpu.engine2d.simd_isa_provider.{simd_isa_fill_const}
use std.nogc_sync_mut.io_runtime.{time_now_unix_micros}

fn main():
    var a: [u32] = [0; 64]
    val t0 = time_now_unix_micros()
    oracle_fill_const(a, 0, 64, 0xFF204060)
    val t1 = time_now_unix_micros()
    simd_isa_fill_const(a, 0, 64, 0xFF204060)
    val t2 = time_now_unix_micros()
    print("scalar_us=" + (t1-t0).to_text() + " simd_us=" + (t2-t1).to_text())
```

Corroborating numeric evidence from the full B2 probe
(`src/app/test/engine2d_jit_timing_probe.spl`, buckets {64,256,1024,4096,16384},
50 iters each): default (nominally-JIT) invocation vs explicit
`SIMPLE_EXECUTION_MODE=interpreter` invocation produced timings within
~1.0x–1.3x of each other on every (kernel, bucket) pair — e.g.
`fill_const bucket=4096`: default `scalar_ns=691504000` vs interpreter
`scalar_ns=531070000` (ratio 1.30x); `src_over bucket=4096`: default
`scalar_ns=21066859000` vs interpreter `scalar_ns=21104698000` (ratio
1.002x). A real Cranelift-JIT-vs-tree-walk-interpreter split is expected to
differ by roughly one to three orders of magnitude (per
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md` and
the fallback banner's own `~100-1000x slowdown` estimate). Numbers this
close are consistent with BOTH invocations having executed via the
interpreter, not with one being genuinely JIT-compiled.

Note the `[jit-fallback]` banner did not reprint on every invocation of the
full probe in this session (Cranelift may deduplicate the message once
already emitted in a warm process) — the numeric ratio above is the
authoritative corroborating signal when the banner is absent.

## Root cause (traced)

`std.nogc_sync_mut.io_runtime` (`src/lib/nogc_sync_mut/io_runtime.spl`)
transitively references `rt_file_is_char_device`, which is not resolvable by
the Cranelift JIT's symbol table in this build. Any module importing
`time_now_unix_micros` from that module (there is no narrower timing-only
import) pulls in the whole `io_runtime` symbol set, including the
unresolved extern, so the JIT backend fails to link the module and falls
back to the interpreter for everything in it — not just the timing call.

## Impact

Any perf/timing probe that measures itself via `time_now_unix_micros` and is
run through `bin/simple run` cannot produce a genuine JIT number on this
binary. This blocks unit B2 as originally scoped ("time under BOTH engines
via `bin/simple run`"): only one real engine (interpreter) is reachable this
way, regardless of which invocation is used.

## Unblock condition

Either (a) resolve/stub `rt_file_is_char_device` in the JIT's runtime symbol
table so `io_runtime` links under Cranelift, or (b) add a JIT-safe narrow
timing primitive (e.g. a standalone extern with no other `io_runtime`
baggage) that a probe can import without pulling in the unresolved symbol.
Until then, B2-style probes should report their engine honestly as
"interpreter (JIT requested, fallback confirmed)" rather than "jit".

## Filed by

Unit B2, `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
2026-08-08.
