# Traceability CLI capture increment — 2026-10-11

STATUS: FAIL (native capture acceptance); protected release admission unavailable.
This is a private implementation increment, not full 20 REQ-TRC / 40 AC-TRC acceptance.

The production standalone command now uses the shared strict qualification SDN codec,
parses all options before input capture, rejects obsolete JSON modes, sends progress
only to stderr, reads bounded UTF-8 inputs once, binds observed configuration and
sorted content digests into a worktree-input identity, and evaluates the materialized
VirtualFiles rather than rereading mutable paths. Completed legacy structural checks
retain qualification=incomplete. Observed no-follow checks are not atomic confinement.

Astra resolved the configuration-allocation-order issue: member count, aggregate bytes,
NUL and per-member limits now precede manifest construction. Early identity failures
use worktree-attempt:unavailable, snapshot.complete=false; this reserved marker claims
no captured subject. Public options/limits/cwd validation precedes attempt allocation.

## Actual execution evidence

Rust bootstrap was used only to construct Phase 2 native binaries, as authorized.
Native binaries executed production code and SSpec assertions. No seed application
execution, placeholder pass or authenticated producer admission is claimed.

- Original CLI baseline: four scenarios visibly failed, then missing --scope triggered
  an unbounded repository scan; outer 30-second timeout ended execution (exit124).
  There is no completed seven-example baseline verdict.
- First production increment: native command built65 modules; real command SSpec
  completed seven examples, zero failures. That executable predates the later
  unavailable-attempt and enumeration-slice revisions; its evidence stays source staged.
- Capture controls: first and diagnostic second runs completed six examples, one
  failure. The diagnostic isolated Unicode/NUL-record acceptance=false.
- Third and final scoped repair cycle: explicit byte slices replaced substring at
  NUL byte offsets; native controls still completed six examples, one failure.
  Five scenarios passed, including actual find output truncated at successful exit,
  constructed options/limits, early failure report encoding, configuration member
  limits and diagnostic construction budget. Unicode/NUL positive control remains red.
- Final native command construction succeeded, but its full CLI acceptance was not
  rerun after the three-cycle cap. Do not transfer prior green evidence to this binary.

Private logs and executables: build/native_probe/traceability-cli-{command,system,limits}-20261011-*.
The final failing control is test/03_system/app/traceability/feature/traceability_capture_limits_spec.spl.
Concrete unresolved defect: doc/08_tracking/bug/traceability_native_unicode_capture_2026-10-11.md.

Astra final scoped source review: PASS, P0=0/P1=0; runtime verdict remains FAIL.
The encoding control constructs a report, not a real failed-cwd command; configuration
control tests the validator, not capture-path invocation order. Cross-file linkage is
not independently exercised by the one-file diagnostic-budget control.

No full runtime/core/MCP/LSP smoke, coverage, latency/RSS, descriptor confinement,
full dispatcher, graph/execution evidence, hooks or Slop acceptance is claimed.
The verified scalar/strict/typed increment is synchronized independently; this CLI
increment remains private because its acceptance is red. No green checks were rerun
without source changes; no further capture repair cycle is authorized by the local cap.
