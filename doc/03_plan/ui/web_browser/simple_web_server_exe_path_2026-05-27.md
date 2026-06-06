# Plan: Simple Web Server — Compiled EXE Path & Interpreter Performance

**Date:** 2026-05-27
**Status:** Phase 1 partial (rt_text_to_i64 fix kept, lib workarounds reverted), Phase 2–3 pending

## Baseline (Interpreter Mode, Single-Threaded)

| Metric | Simple (interpreter) | nginx |
|--------|---------------------|-------|
| RPS (sequential, /api/health) | 1,096 | 199,517 |
| Avg latency | 0.91 ms | 0.208 ms |
| Max latency | 1.13 ms | 6.50 ms |
| Threads | 1 (single) | auto (multi) |
| Concurrency | 1 (sequential) | 50 |

Simple interpreter: 0.55% of nginx RPS. Expected — interpreter overhead + single-threaded + no sendfile.

## Phase 1: Fix Interpreter Blockers (PARTIAL)

### Kept: Pure-Simple text parsing (legitimate fix)
1. **`rt_text_to_i64` extern** — replaced with pure-Simple char_at+arithmetic parsing in:
   - `src/lib/nogc_sync_mut/http_server/parser.spl`
   - `src/lib/nogc_sync_mut/http_server/types.spl`
   - `examples/06_io/simple_web_server/config.spl`

### Reverted: Library degradations (filed as interpreter bugs)
The following workarounds were reverted because they degraded the shared library API.
Bugs filed in `doc/08_tracking/bug/`:

2. **`self.field = value` rejected** → `interpreter_self_field_assign_rejected_2026-05-27.md`
   - Interpreter rejects field mutation in methods; compiled mode works fine

3. **`self.fn_field(args)` confused with method calls** → `interpreter_fn_field_method_confusion_2026-05-27.md`
   - `r.handler(req)` fails because interpreter treats fn-field as method lookup

4. **Semantic thread_spawn_with_args wrapper registration** → `interpreter_thread_spawn_with_args_registration_2026-05-27.md`
   - Old raw extern path was not in interpreter dispatch table; new code uses `thread_spawn_with_args`

5. **`mut fn` syntax** → `parser_mut_fn_syntax_not_supported_2026-05-27.md`
   - Parser does not recognize `mut fn`; may be by design

### Conclusion
Web server requires compiled mode for full functionality. Interpreter mode blocked by bugs 2–4.

## Phase 2: Compiled EXE Path

### Goal
Compile Simple web server to native binary for production performance.

### Steps
1. Resolve all extern stubs needed for compiled mode (`thread_spawn_with_args`, TCP accept)
2. `bin/simple native-build --entry examples/06_io/simple_web_server/main.spl -o build/simple-web-server`
3. Multi-threaded accept loop (restore `thread_spawn_with_args` behind compiled-mode guard)
4. Sendfile routing for static files (already implemented in `sendfile_routing.spl`)
5. Benchmark compiled binary vs nginx with wrk (4 threads, 50 connections)

### Target
- Small responses (JSON health): >50K RPS (25% of nginx)
- Static files: sendfile-bound, should approach nginx

## Phase 3: Interpreter Performance Improvements

### Known Bottlenecks (from ref_interpreter_perf_bottlenecks.md)
1. **debug_state mutex** — global lock on every statement; disable in release interpreter
2. **Value::Str copies** — Rc/Arc refcount instead of clone on every string op
3. **Extern dispatch** — HashMap lookup per call; switch to index table
4. **Expression evaluation cascade** — match chain; flatten to computed goto
5. **Coverage overhead** — per-line tracking; disable unless opted in

### Quick Wins (no compiler changes)
- Connection keep-alive (avoid TCP handshake per request)
- Pre-parse route table (avoid string matching per dispatch)
- Buffer response writes (reduce syscall count)

### Estimated Impact
If bottlenecks 1+2 are fixed: ~5-10x interpreter throughput (5K-10K RPS sequential).
Compiled mode with threads: target 50K+ RPS.
