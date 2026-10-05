# Optional bool binding retains presence type instead of bool value

Actual seed588 diagnostic optional-request-split-seed-probe: compile0, 13/14 checks passed; Some(false) bound by if-val took the true branch19 instead of23. All separate-extension default cases passed. Original frozen packets remain unchanged.

Retained LLVM COFF object71c98b4628c5c8e5.o, inspect_boolean: calls rt_is_some on subject, rt_unwrap_or_self, then rt_is_some on extracted payload. Second presence check incorrectly treats a valid false payload as true. HIR build_if_let_binding_stmts peeled only BoxInt optional types; bool binding kept optional Pointer type. This is not a runtime presence bug.

Repair: type a bool? payload binding as BOOL; MIR decodes tagged boolean through existing rt_value_as_bool after rt_unwrap_or_self. Keep subject presence checks unchanged and do not decode bool via UnboxInt. ANY and non-bool paths remain unchanged. Pure-Simple compiler parity is not established by this bootstrap-specific source fix.

Seven focused native cases cover nil, true/false payloads, returned true/false, and false-presence/nil-absence. Actual fixed-producer LLVM and Cranelift execution is pending. No native PASS or release readiness claimed from source checks.