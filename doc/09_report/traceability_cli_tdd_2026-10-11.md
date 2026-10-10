# Traceability CLI capture increment — 2026-10-11

STATUS: WARN (source-staged provider evidence; full acceptance/admission unavailable).
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

## Historical execution evidence — superseded by the follow-up below

This section describes the first bounded capture cycle and its then-current
FAIL verdict. Present-tense failure notes below are historical; the follow-up
records the fixture correction and current WARN. Original counts stay unchanged.

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

## Follow-up: fixture transport and actual provider controls

A separate bounded investigation identified malformed test input, not a proven
production Unicode failure. Result/text nil coalescing rendered the entire
Result::Ok payload instead of extracting its text; the terminal NUL was inside
parentheses. Explicit Ok matching produced the expected one-byte NUL. The old
6/1 remains historical; the capped suite was not rerun or relabeled green.

- New fixture regression: native3 examples/0 failures. It asserts exact payload
  bytes, Unicode/newline/marker-like names, adjacent NUL records, empty records
  and incomplete final framing.
- New provider suite: actual legacy command6 examples/5 failures; current final
  production command6 examples/0 failures. The digest-owner case passed at both
  stages. The exclusively owned fingerprint fixture was restored to its recorded
  initial bytes before changing command stages, because the test mutates it.
- Actual inputs:4137-byte configuration with a4097-byte member; real symbolic
  file;10-byte file containing malformed UTF-8; real Unicode/newline filename;
  same-path input changed after two byte-identical unchanged captures.
- Fixed SHA256 empty/abc vectors and chunked a+bc digest passed through the actual
  shared owners. No performance or general crypto certification is implied.
- Astra reviewed the new source/oracles and independently inspected the fixtures:
  PASS P0=0/P1=0; evidence qualification WARN. Refusal assertions use broad codes,
  so preserve file-type/content/hash evidence and do not claim distinct provider
  cause classification. The Unicode file was selected directly, not discovered
  through find; the new unit test separately qualifies NUL decoder transport.

Current actual provider properties supplement the earlier CLI7/0; they do not
transfer that earlier suite's verdict to final source. No old fixture-dependent
assertion receives retrospective validation. Full dispatcher, unavailable-cwd
command, cross-file graph closure, runner/receipt trust and all20/40 remain open.

Source/probe/invocation receipts: private
build/session/traceability-fixture-provider-20261011/evidence.json. These are
host diagnostic records, not Simple trace receipt admission or signed provenance.
