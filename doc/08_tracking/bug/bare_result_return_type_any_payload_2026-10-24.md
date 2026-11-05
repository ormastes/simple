# bare_result_return_type_any_payload

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: unsupported Result unwrap/unwrap_err payload type: payload is Any (linker_wrapper_helpers.spl:77): find_runtime_binary declared -> Result with no type arguments.

Workaround (tagged `@workaround bug=bare_result_return_type_any_payload_2026-10-24`): spell Result<text, text> (src/compiler/70.backend/linker/linker_wrapper_helpers.spl).

Root fix location: src/compiler/80.driver/driver_pipeline_lowering.spl (Result unwrap payload check) - either reject bare Result at type check or infer from returns.

## Resolution (2026-11-05): closed by design
A bare `-> Result` has an Any payload. `lower_result_unwrap_core` rejects an Any
payload fail-closed (policy: Any is an error outside unsafe) and the RTI row
erases it to `b:any` (rti007 design), so there is no compiler defect to fix:
the spelled `Result<T, E>` is the required source form and no bare `-> Result:`
remains in src/. Guard: `test/01_unit/compiler/mir/bare_result_return_spelled_guard_spec.spl`
(detector self-test, find_runtime_binary spelling, sibling linker sources).
