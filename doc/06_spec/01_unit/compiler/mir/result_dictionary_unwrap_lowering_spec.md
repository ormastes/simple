# Result dictionary MIR ownership and failure paths

Authored manual for
`test/01_unit/compiler/mir/result_dictionary_unwrap_lowering_spec.spl`.
REQ-ENUM-RESULT-DICT. Four scenarios authored; execution UNRUN.

The fixture calls production `lower_result_unwrap_core` with a prelowered
receiver. Its deliberately invalid source expression must never be evaluated
again; success therefore checks the existing prelowered path's contract.

| Scenario | Required observation |
|---|---|
| Typed raw dictionary extraction | Independently expected text-key and integer/float/text-value MIR types; exact remembered HIR; dictionary/tagged flags and value metadata; direct copy from payload call to result local |
| Runtime operations | Exactly discriminant, payload and panic calls; no dictionary allocation/clone/reboxing runtime call |
| Tag and mismatch paths | Ok uses 0, Err uses 1; exactly one mismatch block ends in Abort with the precise direction-specific message; no zero payload assignment |
| Rejections | Default-bearing Dict and unsupported Any payloads emit exact fatal unwrap/unwrap_err diagnostics before any runtime call; supported Optional carriers have a separate spec |
| Existing scalar boundary | No-default scalar mismatch aborts; a scalar default retains a normal merge edge |

Both direction checks use actual MIR instructions and terminators, not source
strings. The independent runtime spec checks real dictionary contents and the
module-index consumer. MIR structure does not qualify native traps, C bootstrap
emission, measured allocations, RSS, latency, or general schema evolution.
