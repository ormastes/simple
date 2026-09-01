# Render 8K80 A1 adapter attribution

Status: **TEST_BLOCKED** — the executable SSpec is ready, but no admitted
pure-Simple CLI is available for runtime execution, `spipe-docgen`, or
`sspec-maintain`. This checked-in manual mirrors the intended operator flow and
must be regenerated and reviewed from the executable spec when an admitted CLI
is deployed. It is not generated-runtime evidence.

## Purpose and audience

This manual protects the completed A1 physical-adapter attribution criterion.
It is for rendering operators and reviewers who must distinguish stable device
identity from physical-display or scanout proof.

## Preconditions

- Work from the repository root.
- Use an admitted pure-Simple CLI; never use the Rust bootstrap seed.
- Ensure `sh`, `grep`, and the checked-in rendering wrappers are available.
- GPU hardware and an 8K display are not required for these bounded scenarios.

## Operator workflow

1. Execute
   `test/03_system/gui/wm_compare/render_8k80_a1_adapter_attribution_spec.spl`
   with the admitted CLI.
2. Observe the physical-wrapper self-test validating its positive and
   deliberate-red identity-correlation matrix.
3. Confirm the durable RTX A6000 fingerprint is bound to stable selected-device
   identity hash `666008366`.
4. Confirm A6 and A8 remain open and Xvfb remains inadmissible as physical
   display or scanout evidence.
5. Observe the forced-unreachable-display scenario return exit `2` and the
   typed `physical-x11-display-unreachable` blocker.

## Scenario narratives

### Durable identity correlation

- Run the physical-wrapper identity correlation self-test.
- Require both window and physical-wrapper self-test PASS markers.
- Read the durable report.
- Require the exact NVIDIA RTX A6000 vendor, device, driver, API, and stable
  selected-device identity hash.

### Attribution without physical promotion

- Read the canonical A1–A8 ledger.
- Require A1 checked.
- Require A6 and A8 unchecked.
- Require both the plan and report to retain the Xvfb/scanout exclusion.

### Unreachable physical display

- Invoke the production wrapper with a deliberately unreachable display.
- Require exit `2`, `status=blocked`, `todo=TODO684`, and
  `reason=physical-x11-display-unreachable`.
- Any zero exit or PASS marker is a failure.

## Requirement traceability

| Requirement | Scenario coverage | Expected result |
|---|---|---|
| REQ-R8KC-004 | Positive, edge, and error | Exact fields are retained; scope drift and unavailable-device receipt promotion are rejected |
| REQ-R8KC-006 | Positive, edge, and error | A1 stays bounded; A6/A8 remain open; missing physical display is blocked |
| NFR-R8KC-004 | Positive, edge, and error | Valid correlation passes while invalid/unavailable inputs fail closed |
| NFR-R8KC-006 | Positive, edge, and error | Xvfb and an unreachable display never become physical scanout evidence |

## Quality scorecard

| Component | Current state |
|---|---|
| Purpose and audience | Present |
| Preconditions | Present |
| Visible step flow | Present in executable spec and mirrored above |
| Positive/edge/error coverage | Present |
| Requirement traceability | Present |
| Evidence/provenance | Source paths and expected markers documented |
| Runtime/docgen/maintenance score | TEST_BLOCKED pending admitted CLI |

## Findings and remediation

- `TEST_BLOCKED`: tracked candidate
  `release/x86_64-unknown-linux-gnu/simple` (SHA-256
  `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`)
  exits `139` for `test --help`; the only alternate binary identifies itself as
  a Rust bootstrap seed.
- Remediation: deploy an admitted pure-Simple CLI, run the focused spec once,
  run `sspec-maintain scan` once, regenerate this manual with `spipe-docgen`,
  and review all seven maintenance scores and the zero-stub result.

## Evidence and provenance

- Executable spec:
  `test/03_system/gui/wm_compare/render_8k80_a1_adapter_attribution_spec.spl`
- Acceptance ledger:
  `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`
- Durable report:
  `doc/09_report/engine2d_vulkan_clear_8k_evidence_2026-08-12.md`
- Production wrapper:
  `scripts/check/check-render-perf-physical-8k80-hardware.shs`

## Compatibility and limitations

This coverage proves A1 attribution and fail-closed classification only. It
does not prove A4/A5 performance, a physical 8K80 mode, presentation, or
captured scanout. A hand-maintained TEST_BLOCKED manual is not a substitute for
future admitted runtime and generated-manual evidence.
