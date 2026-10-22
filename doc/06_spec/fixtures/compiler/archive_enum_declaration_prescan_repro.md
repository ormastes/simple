# Archive enum declaration prescan: direct diagnostic

Executable entry: `test/fixtures/compiler/archive_enum_declaration_prescan_repro.spl`.
This direct fail-fast diagnostic uses actual frontend, HIR, artifact projection,
and MIR APIs; it uses no SSpec runner or final archive admission.

## Assertions

- Rich provider declarations retain explicit discriminants 7 and 12 and implicit
  successor 13, runtime names, generic flags, ordered named fields, and default 9.
  The default is an explicit temporary HIR overlay from a genuinely parsed
  `default_count` literal before actual artifact projection. The flat parser
  drops enum field defaults; this diagnostic does not claim parser support.
  See `doc/bug_report/enum_named_payload_default_dropped_2026_10_16.md`.
- Semantic unit classification accepts a real frontend unit; a nonempty tuple
  and absent slot-name metadata cannot classify as units.
- Prescan retains no provider-local payload HirTypes; unused consumer enums
  remain unhydrated. Actual payload demand relocates Packet rather than a decoy
  into two fresh consumers with colliding numeric IDs.
- A qualified foreign payload/runtime demand preserves a local Choice.Shadow.
- A genuine function fragment whose first constructor use occurs inside its
  lambda emits a nonempty `__lambda_lift_` body without lowering errors.
- A known unrelated typed capture adds no enum-test MIR arm. This structural
  assertion does not claim redundant-catch-all diagnostics are repaired.
- Removing a genuine explicit-discriminant artifact rejects hydration and emits
  an actual fatal diagnostic instead of silently omitting the variant.

The phase barrier decodes exact artifacts once. Consumer payload access uses
ID-free repository indexes and the existing provider type relocator; global
variant-owner scans do not hydrate payloads. Prior consumer type arrays are
cleared, and lifted lambdas inherit the deferred indexes.

## Verification status

**NOT EXECUTED for the repair.** Independent static review found missing lambda
state propagation, which was corrected and re-reviewed. Static review supplies
no runtime qualification.

The smaller baseline fixture's A174 native build timed out after 1,800 seconds
(guard exit 124). All HIR workers completed without failed or unfinished
modules; no fixture assertion executed. Postflight confirmed unchanged source
and fixture. A coordinated read-only LLDB sample detached without catching a
fault; this run supplies no timing qualification. An earlier `run` attempt
failed at command dispatch and is not a reproduced enum failure. Baseline
assertion evidence and repaired execution remain pending. A success claim needs
all assertions and the final PASS print; process status alone is insufficient.
No fixed claim or release PASS is established.
