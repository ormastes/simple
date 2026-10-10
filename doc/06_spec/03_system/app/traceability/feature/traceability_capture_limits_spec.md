# Bound structural capture

Manual companion to test/03_system/app/traceability/feature/traceability_capture_limits_spec.spl.
Requirement: REQ-TRC-010; partial AC015 controls, no full acceptance claim.
Evidence: doc/09_report/traceability_cli_tdd_2026-10-11.md.

1. Reject constructed options and invalid limits before attempt allocation. Encode
   the reserved unavailable-attempt marker as an incomplete typed report.
2. Reject NUL arguments and missing scope; retain quiet after later dot flags.
3. Require complete NUL records, successful status, empty stderr and capture/count
   bounds. Preserve a Unicode/newline filename even when it resembles marker text.
4. Run actual find with an eight-byte output cap; reject truncated capture at exit0.
5. Reject an oversized configuration member using the shared validator.
6. Reject diagnostic budget5 for one input; accept reviewed bound6.

Actual final native result: six examples, one failure. The Unicode/NUL positive
control remains red after three scoped cycles. No full failed-cwd, configuration
capture-boundary or cross-file linkage execution is claimed. Manual authored from
executable steps; no rendering or manual quality admission is claimed.
