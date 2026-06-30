# BUG: standalone SMF cannot run interp-fallback functions (string interpolation, slices)

- **ID:** `smf_standalone_interp_fallback_functions_unavailable`
- **Severity:** P2 (feature-scale gap; blocks SMF benchmark/run of any workload whose hot path
  uses string interpolation or other interp-routed constructs — e.g. the web http server)
- **Found:** 2026-06-14, AC-5 web benchmark SMF emission (perf-opt umbrella).
- **Status:** OPEN — honestly omitted; `web_bench_driver` graceful-skips the smf plane with a
  printed reason (no fabricated rows). Script-plane rows still emit.

## Symptom
`bin/simple compile X.spl -o X.smf && bin/simple run X.smf` aborts at runtime with
`rt_interp_call: function not found: <fn>` (E3008) for any function that was routed to
`InterpCall` by the hybrid transform. Example: `serialize_response`
(`src/lib/nogc_sync_mut/http_server/response.spl:20`) builds the HTTP wire string with genuine
interpolation (`"HTTP/1.1 {status_code} {reason}\r\n"`), which correctly triggers
`FallbackReason::StringOps` → the function is marked non-compilable → its call sites become
`InterpCall`. JIT / in-process runs seed the interpreter snapshot so the call resolves, but a
**standalone SMF has no snapshot seeding**, so the runtime call has no target.

## Distinct from
- `interp_qualified_enum_is_payload_variant` / the WAL fix — unrelated (enum `is`).
- The os pure-literal-FString fix (commit `36a4eccc3ef`) — that fixed FStrings with *no*
  interpolation (which should never fall back). Genuinely-interpolated FStrings legitimately need
  the runtime string-format path; this gap is about making that path available in a standalone SMF.
- The `rt_io_tcp_*` socket-extern registry gap (this commit's shim) — that was a load-time
  *undefined-symbol* relocation failure; this is a separate run-time *missing-function* failure that
  only surfaces once the symbol resolves and execution begins.

## Repro
`bin/simple compile test/05_perf/web/web_smf_workload.spl -o /tmp/web.smf && bin/simple run /tmp/web.smf`
→ no `RESULT` lines; stderr repeats `function not found: serialize_response`.

## Fix options (both feature-scale — do not band-aid the workload)
1. **Native string-format codegen** — lower interpolated FStrings to a native format call so the
   function compiles instead of falling back. Removes the `StringOps` fallback entirely.
2. **SMF interp-snapshot seeding** — embed the interpreter snapshot (or the needed function bodies)
   into the SMF so `rt_interp_call` can resolve interp-routed functions in a standalone run.

Until one lands, SMF benchmark emission is limited to workloads whose hot path is natively
compilable; interpolation-heavy ops (http serialize) stay honestly omitted.
