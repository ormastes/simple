# Native Unicode/NUL capture control remains red

Status: RESOLVED as a malformed fixture; original failure evidence retained. Scope: user-authorized Phase 2 native traceability capture.

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

## Follow-up diagnosis and corrected evidence

A distinct native transport probe observed that
`validated_utf8_bytes_to_text_linear([0u8]) ?? ""` did not extract the Result
payload: its receiver length was -1, and concatenation rendered Result::Ok(...)
with the NUL inside parentheses. The enumeration wire therefore had no terminal
NUL. Matching Ok(value) instead yielded exactly len1/bytes[0]. This explains
the positive fixture's failure without establishing a production Unicode defect
or a compiler/runtime root cause. The misuse is recorded separately in
phase2_result_text_coalescing_type_hazard_2026-10-11.md.

The capped suite's historical6/1 is unchanged and was not rerun. The corrected
fixture helper asserts actual byte identity. A new three-case native fixture
regression passed3/0, including Unicode/newline preservation, adjacent records,
empty record rejection and incomplete framing. A separate actual production
provider suite showed legacy6/5 then current6/0; the real Unicode/newline filename
was selected directly and preserved in canonical typed SDN. It does not establish
find transporting Unicode filenames. No earlier fixture-dependent PASS is
retroactively validated; all20REQ/40AC and broad runtime/admission remain open.

Probe: build/native_probe/traceability-text-transport-20261011/observations.log.
Regression: test/01_unit/app/traceability/traceability_nul_fixture_spec.spl.
Provider: test/03_system/app/traceability/feature/traceability_provider_spec.spl.
