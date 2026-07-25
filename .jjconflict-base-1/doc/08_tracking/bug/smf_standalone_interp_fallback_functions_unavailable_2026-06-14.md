# BUG: standalone SMF cannot run interpreter-fallback functions

- **ID:** `smf_standalone_interp_fallback_functions_unavailable`
- **Severity:** P2 (feature-scale gap; blocks SMF benchmark/run of any workload whose hot path
  uses string interpolation or other interp-routed constructs — e.g. the web http server)
- **Found:** 2026-06-14, AC-5 web benchmark SMF emission (perf-opt umbrella).
- **Status:** SOURCE FIXED — fail-closed AOT emission, multi-section SMF layout, and fresh-process
  interpolated-helper execution pass focused regression coverage.

## Symptom
The Rust seed's `bin/simple compile X.spl -o X.smf && bin/simple run X.smf` aborted at runtime with
`rt_interp_call: function not found: <fn>` (E3008) for any function that was routed to
`InterpCall` by the hybrid transform. Example: `serialize_response`
(`src/lib/nogc_sync_mut/http_server/response.spl:20`) builds the HTTP wire string with genuine
interpolation (`"HTTP/1.1 {status_code} {reason}\r\n"`). The SMF emitter incorrectly used the
hybrid-JIT classifier, so `FallbackReason::StringOps` marked the function non-compilable and its
call sites became `InterpCall`. JIT / in-process runs seed the interpreter snapshot, but a
**standalone SMF has no snapshot seeding**, so the runtime call has no target.

The pure-Simple compiler already lowers interpolation and text slices directly to runtime calls;
it does not produce `InterpCall`. The defect was confined to the Rust bootstrap seed's two SMF
emission paths.

The first standalone helper replay also exposed an independent loader-format defect: Cranelift
emits separate, identically named `.text` sections, while SMF originally serialized their symbols
and relocations as if every offset were relative to one section. The object parser now flattens
code offsets by stable object section index and preserves section-target relocations.

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

## Fix
Both host and target-specific SMF emitters now classify with `CompilabilityMode::AotNative`.
Interpolation therefore follows its existing native runtime-call lowering. Any construct that
still genuinely requires the interpreter is rejected with a sorted diagnostic before MIR can be
rewritten to `InterpCall`; no invalid SMF artifact is written.

`runner_tests.rs` covers a fresh-process interpolated helper, a fail-closed host `TryOperator`, and
target-path rejection descriptors for Linux, macOS, Windows, FreeBSD, ARM, AArch64, and RISC-V.
The integration tests currently execute in Linux x86_64 CI; wider native-host scheduling remains a
separate coverage gap because that integration-test crate is architecture-gated.
