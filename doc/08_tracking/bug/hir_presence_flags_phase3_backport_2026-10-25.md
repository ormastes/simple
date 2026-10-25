# Missing HIR presence flags: Phase 3 backport

Source: merged release/1.0.0 PR #4785 (`f660f01b7f83b39706f48b23ed3d0eb1c0199dcd`).
The bounded comparison against release_phase3 `f48b1d4a8166` found the affected
constructor arguments absent; this is not covered by decoder hardening #4772.

Five production files receive the original thirteen constructor arguments.
Parser presence flags are copied where available; lambda parameters and
specialization metadata receive explicit false. Bitfield type presence derives
from the actual lowered optional payload. Optional payload fields remain.
An omitted boolean can otherwise remain nil and encode as `N`, preventing
faithful HIR cache admission. Decoder refusal is not a substitute for producing
the correct concrete boolean in lowered HIR.

Exact source review found an upstream donor defect: unconditional bitfield
`has_type_: true` disagrees with nil payloads on reserved/untyped fields. The
backport corrects that argument rather than copying the defect. The lowering
uses presence binds for the source type and resulting lowered type. A real
typed-versus-reserved owner fixture checks both values and stable roundtrips.

The original five-case source-coverage spec is retained with its bitfield
expectation corrected to match actual payload presence. Its new
behavioral counterpart parses/lowers an actual struct/trait, checks false-valued
metadata and field presence directly, and checks those values and stable bytes
after the hardened bounded generated decoder. Canonical availability stays
false; no codec regeneration or generated artifact change is needed.

Runtime execution of both specs and compiler/native/core checks is **UNRUN**.
The admitted `8cd080ef9b7d59794d161beaee33c04260ca643511c58d9c19d125d6092cce1e`
is compiler-only, not a qualified test CLI. No new native build, Hello rerun,
bootstrap input change or heavy test is authorized for this backport.

This is a next-source-freeze fix. It does not change the live `83be` source,
`8cd` output/admission, planner, runtime capsule, or watcher, and it does not
resolve the current external-heavy admission refusal. Performance and RSS are
unmeasured; the production delta adds thirteen constructor values only.
