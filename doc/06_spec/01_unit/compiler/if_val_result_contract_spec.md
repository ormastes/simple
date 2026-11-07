# Result presence-binding contract

Executable specification: `test/01_unit/compiler/if_val_result_contract_spec.spl`.
Requirement: REQ-IF-VAL-RESULT-CONTRACT.

Bare identifier presence binding of a directly typed Result must report a
diagnostic before the binder is admitted. Both an annotated Result parameter
and a Result-returning call are exercised, including if-val and while-val.
The diagnostic directs callers to explicit Ok/Err matching or Result.ok.?.
Optional Result payloads and the documented Result.ok.? projection remain legal.
Explicit authored Result .? in both if-val and while-val is also lowered through
the real frontend/HIR pipeline; it must survive bridge provenance coalescing.
The flat core interpreter is invoked directly for bare Ok/Err if-val and Ok
while-val diagnostic checks, plus payload-value checks for explicit .? and
Some(Result). This exercises the actual provider rather than a seed substitute.

This companion is a source-level test plan. Execution is UNRUN pending campaign
resource admission; it is not passing evidence.
