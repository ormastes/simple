# Match routing rereads an erased normalized arm carrier

Status: source candidate; native reproduction and qualification **UNRUN**.

## Observed failure

The frozen 916 source compiled by producer 3bd reports B5b multiple wildcard
and wildcard/binding defaults in the slang_pack dependency closure and in
the Phase3 action_identity/artifact_receipt object attempts. The slang_pack
log SHA256 is
`87001134521ff75be7d6e9936e812db2cd4ff490fb4d428fa2b5686c3951e1e4`.
These messages have no function spans. They do not establish that every
reported default is a misclassified enum, or identify a single SDN function.

## Source-proven exposure and repair

`lower_match_case` documents a composite-array element erasure failure when
reading `norm_arms[i].pattern.kind` after rebuilding the array. Its existing
direct Enum/Wildcard-only route avoids that read. Mixed enum/capture-default
matches and bare unit normalization still perform it.

Retain the enum-presence flag from the original explicitly typed arm scan;
set it when a binding is actually normalized into an enum. This eliminates
the redundant normalized-array classification pass. Arms, qualified owner
lookup, ambiguity handling, ordering, payloads, guards and runtime dispatch
are unchanged. This repairs the identified exposure; historical failure
attribution remains pending an actual native comparison.

The enum route also previously replaced its default body silently when a
second wildcard/binding appeared. It now records an error and returns, like
the existing integer route. No default arm is dropped to make a build pass.

## Reproduction and neighboring checks

- `test/01_unit/compiler/mir/match_arm_route_spec.spl`: eight actual
  parser/HIR/MIR cases; positive enum cases require emitted discriminant
  calls and zero errors, integer control requires no enum dispatch, and
  duplicate defaults require the exact applicable diagnostic.
- `test/fixtures/compiler/match_arm_route/main.spl`: nine native runtime
  assertions covering selected/fallback unit arms, payload and integer
  captures. Run both Cranelift and LLVM with the candidate compiler.
- `duplicate_enum_default.spl`: compile-negative control; accept only the
  intended MIR diagnostic, never an unrelated compiler failure.

Memory/logic: the original and normalized arm carriers retain their existing
lifetimes and ownership; no new reference or payload copy is introduced.
Performance: removes one O(arms) traversal and adds one scalar flag update
per normalized binding. No measured speed/RSS claim is made. Both-backend
native checks, candidate compiler-code tests, and matched peak-RSS/timing
remain pending admitted capacity. No running source, cache or producer was
modified. Existing B5b safeguards remain release blocking.
