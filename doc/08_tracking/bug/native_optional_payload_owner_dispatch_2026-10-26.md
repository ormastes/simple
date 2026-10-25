# Native optional enum payload dispatch blocks HIR substitution

Status: OPEN — reduced native reproduction, no repair or overall PASS.
Canonical bug DB reconciliation: pending (no admitted general pure-Simple
bug DB command runner was used). Owner: compiler MIR optional-pattern typing
and monomorphization HIR substitution.

## Trigger and evidence

The retained `C:/dev/wt-enumid/build/lane-D-new-mcl/build.log` fails in
`hs_enum_payload` and `hs_pattern_payload` of
`src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl` at lines 360/378.
The optional argument is matched against bare Tuple/Struct payload variants,
Some(p), and nil in the same match. Duplicate payload names occur in both
HirEnumPayload and HirPatternPayload.

A one-module reduced native probe reproduces ambiguous Tuple/Struct owners.
Qualifying the payload owners still fails because the scrutinee is Option;
Some and nil arms are subsequently interpreted under the payload owner.
The compiler must preserve the optional/payload owner distinction and either
handle the documented source contract correctly or report a consistent type
error; qualification alone cannot fix this caller.

Sources: `C:/dev/wt-s2new/test/fixtures/compiler/optional_payload_owner_20261026/`.
Logs/rc: `C:/dev/wt-s2new/build/optional-payload-owner-20261026/`.
Native producer SHA-256:
`acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`.
Target: Windows GNU, LLVM, core-c-bootstrap. Both bare and qualified probes
exit 1 after MIR with no generic specializations involved. An explicit
unwrapping control passed MIR and object emission, then failed canonical
link configuration. A manual link also failed on missing runtime/startup
closure; runtime semantics remain unverified. No source workaround has
been installed or retired.

## Acceptance

- Preserve optional absence, explicit Some, and implicit optional conversion.
- Preserve distinct nominal owners for same-named Tuple/Struct variants.
- Substitute every HIR expression and pattern payload, including a second
  pass over previously substituted HIR; retain fail-loud unhandled cases.
- Qualify the actual changed compiler with native behavior and the existing
  hir_subst_body executable spec; do not claim SPipe PASS from these native
  diagnostic fixtures.
- Retry only the affected failed compiler closure after a concrete repair;
  retain independent failures and compatible cache products.

See [reconciliation evidence](../../03_plan/evidence/cache_perfile_phase3_reconciliation_2026-10-26.md).
