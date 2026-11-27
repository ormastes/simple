# BUG: standalone SMF cannot run interp-fallback functions (string interpolation, slices)

- **ID:** `smf_standalone_interp_fallback_functions_unavailable`
- **Severity:** P2 (feature-scale gap; blocks SMF benchmark/run of any workload whose hot path
  uses string interpolation or other interp-routed constructs — e.g. the web http server)
- **Found:** 2026-06-14, AC-5 web benchmark SMF emission (perf-opt umbrella).
- **Status:** OPEN (re-triaged 2026-09-13 — see the note at the end of this file) — honestly omitted; `web_bench_driver` graceful-skips the smf plane with a
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

## Triage 2026-09-13 — LEFT OPEN (SMF compilation is broken outright on this host)

- **measured** (Rust seed `bin/simple` v1.0.0-rc.1, Windows): the repro cannot even reach the reported failure. `bin/simple compile <file>.spl -o <file>.smf` on a three-line function whose body is a genuinely interpolated FString fails at codegen: `Failed to preserve SMF imports/relocations from object code: Invalid data: Failed to parse object file: Invalid section: relocation source section .rdata$.refptr is not executable code`. No `.smf` is produced, so `rt_interp_call: function not found` was never reached.
- **inferred**: that COFF `.rdata$.refptr` failure is a separate Windows SMF-emission defect, not this bug. It does mean the standalone-SMF lane is entirely unavailable here.
- **inferred**: neither of the two fix options has landed — native string-format codegen would have to remove the `FallbackReason::StringOps` route, and SMF interp-snapshot seeding would have to embed the snapshot; nothing in the entry or the tree indicates either.
- Verdict: OPEN.

## 2026-11-07 — fix implemented (round 15, work/r15-interp-design-20261107)

- Re-measured on the release tip seed (Windows): an interpolated-FString
  function now compiles natively and `compile X.spl -o X.smf && run X.smf`
  prints the interpolation (`hello smf 7`, exit 0) — the 2026-09-13 COFF
  `.rdata$.refptr` failure did NOT reproduce on this seed. The remaining
  gap was the compile-time gate `standalone_smf_fallback_error`, which
  refused any file-backed module containing an interpreter-only function.
- Fix: new SMF section `.interp_snapshot` (`SectionType::InterpSnapshot = 17`,
  Rust `common/src/smf/section.rs` and spl twin `70.backend/linker/smf_writer.spl`).
  A file-backed compile with interpreter-only functions now applies the
  hybrid transform and embeds a JSON record `{"version":1,"path","source"}`
  pinning the entry source it was compiled from
  (`pipeline/execution.rs::prepare_smf_interp_fallback`). The runtime loader
  surfaces the payload as `LoadedModule::interp_snapshot`; the driver's
  `execute_and_gc` seeds the interpreter definitions from it
  (`seed_interpreter_from_smf_snapshot`: pinned entry on disk when its text
  matches byte-for-byte, otherwise the embedded text materialised in a temp
  dir, flattened through the same `load_module_with_imports` the JIT lane
  uses) before `main` runs. In-memory and WASM modules keep the fail-closed
  diagnostic (nothing to pin / no host interpreter).
- Repro: `smf_with_interp_fallback_function_runs_through_embedded_snapshot`
  (driver `exec_core.rs`) and
  `file_backed_smf_with_interp_fallback_embeds_snapshot_section`
  (compiler `pipeline/execution.rs`). Prevention:
  `smf_interp_snapshot_survives_source_removal_and_is_absent_without_fallback`,
  `interp_snapshot_requires_a_file_backed_entry_and_is_absent_without_fallback`,
  `interp_snapshot_payload_round_trips_and_rejects_unknown_version`.
- Two bridge defects surfaced once the snapshot made routed calls reachable
  (both fixed here, both would have hit any `rt_interp_call` consumer):
  (1) the seeded state never ran `initialize_extern_functions()`, so a routed
  body could not resolve prelude externs (`function print not found`), and
  (2) `interpreter_sffi::call_interpreted_function` executed the body with a
  bare `exec_block` + `control_to_value`, which drops the implicit
  last-expression value (`if c: 7 else: 3` answered NIL, decoded as 3 by the
  native caller). It now delegates to `exec_function_with_values`.
  (3) `codegen/instr/body.rs::build_vreg_types` had no `InterpCall` arm, so a
  plain user function's routed-call dest carried no scalar type and
  `compile_interp_call` left the bridge's TAGGED RuntimeValue in the vreg
  (`-> i64` callee answering 7 reached the caller as 56). The dest is now
  stamped from `function_return_types` exactly like a plain `Call`
  (`boxed_result` returns stay unstamped and boxed).
