# Single-field enum constructor boxes Bool payloads as integers

Status: OPEN (P1) — source-level owner and representation mismatch identified; no native reproduction or production fix claimed.

## Static owner finding

In `src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`,
`MirLowerer::lower_call_expr` handles a single constructor argument in the
`arg_regs.len() == 1` branch. Its `needs_box` predicate includes
`TypeId::BOOL`, and the following fallback emits `MirInst::BoxInt`. For an
enum-with payload this encodes Bool as an integer-tagged value rather than the
runtime's tagged-boolean representation. The current multi-field enum fix does
not modify this separate single-field branch.

The static source owner review was performed against the latest release source
plus the landed multi-field patch. It found the one-field branch still includes
Bool in `needs_box` while the patched multi-field branch uses the canonical
boolean boxer. This is source evidence only: no native test of this exact
single-field path has been run, so the defect remains a candidate pending a
focused failing/pass-after regression.

The targeted regression should construct a single-field enum carrying both
false and true, then verify pattern payload and equality semantics without
confounding the multi-field or typed-array paths. Do not infer broader enum or
tuple getter failure from this static finding.
