# Native Unicode/NUL capture control remains red

Status: OPEN. Scope: user-authorized Phase 2 native traceability capture.

Reproducer: build and execute
`test/03_system/app/traceability/feature/traceability_capture_limits_spec.spl` through
its native entry closure. The enumeration positive control combines a UTF-8 lambda,
a newline, marker-like filename text, and terminal NUL. Expected: exactly one path,
byte-identical to the authored filename. Actual: acceptance=false; six examples,
one failure. Both substring and explicit byte-slice implementations failed across
three bounded cycles. No root cause or compiler/runtime fix is established.

Actual successful-exit find truncation is separately rejected correctly. CLI ASCII
fixture scenarios passed at an earlier source stage. Those results do not qualify
Unicode capture or the final revised command. A subsequent scoped investigation
must distinguish byte transport, source literal transport, slicing and equality
before changing any runtime implementation. The assertion remains enabled.

Evidence: private build/native_probe/traceability-cli-limits-20261011-{green,repair2,repair3}.
Related native verdict defect: phase2_native_sspec_fail_ignored_2026-10-11.md;
this spec uses built-in assertions and reports its actual failure count.
