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


## Candidate repair and corrected link diagnosis

The canonical native linker succeeds with an absolute bootstrap-owned CC path;
the reduced unwrapped executable prints `7 8 0`. The earlier manual links omitted
required canonical C/runtime-entry inputs; their archive errors are not proof
of a runtime-provider defect. The original logs remain historical diagnostics.

A candidate now unwraps both optional payloads before exhaustive owner-qualified
matches. Unit regression scenarios add direct/Some tuple/struct payloads,
second-pass stability and absence. A separate native fixture imports the real
substitution functions. Actual-owner native qualification and the general
SSpec/manual gate remain pending; this bug is still OPEN.


## Workaround-first record

- Stable bug record ID: `native_optional_payload_owner_dispatch_2026_10_26`.
- Underlying compiler defect remains OPEN; canonical DB reconciliation pending.
- Workaround blocks: `hs_enum_payload` and `hs_pattern_payload` presence binding.
- Intended-code recovery: `b9f082ef085d6656ad78b9812a3f7335dc29cb5b`, original mixed
  optional/payload patterns in the same source file. Restore only after the
  compiler owner is fixed and original-form behavior is qualified.
- Root-fix owner: root, MIR optional-pattern owner resolution, after the
  workaround and Phase 3 route are qualified.
- The actual-owner expression fixture built a 124-module closure with the
  existing admitted Stage 2, exited 0, and ran with output
  `optional payload substitution: 5 cases, 2 passes each` (run rc=0).
  This checks direct/Some tuple/struct payloads, absence and second-pass stability.
- Producer SHA-256 remains
  `acfedbebd1db457efc0f8d1b0b3020dfa20711157bc090334c1b523a6a228779`;
  no Phase 2 rebuild was needed. The successful source snapshot precedes only
  the workaround marker comments; the presence-binding logic is unchanged.
- A separate pattern fixture is prepared for an 80-job build; its runtime
  outcome is not yet claimed. The existing SSpec additions are unrun because
  a qualified general full-CLI runner is unavailable.

Workaround commit: `9bebc55105d` on `work/phase3-optional-payload-20261026`
(the source annotations carry the stable bug ID and recovery base above).
The commit is local pending remaining qualification and root review.


Pattern qualification completed: requested jobs=80; actual production-owner
124-module fixture native build rc=0 and runtime rc=0, with output
`optional pattern substitution: 5 cases, 2 passes each`. Both touched payload
helpers now have focused native runtime evidence. General SSpec/manual/core
CLI gates remain TEST_BLOCKED; overall Phase 3 and root-fix status stay OPEN.
