# Post-monomorphization HIR type transport corruption (B6)

## Status

Candidate fix implemented; bootstrap acceptance remains open. This blocker is
separate from AVX-512 instruction selection.

## Reproduction evidence

The retained B6 frontend smoke log at
`C:\b6\stage3\x86_64-pc-windows-gnu\stage2-sanity.env.frontend-failure.log`
records three bounded pairs of:

- `[post-mono-type-transport] malformed_hir_type at walk_type`
- `[post-mono-verify] unhandled HirTypeKind variant at walk_type`

All receipts name `scripts/check/cert/redeploy_gate/fixtures/hello_world.spl.main`.
Monomorphization continues after the receipts, so this is distinct from the
later AVX-512 owner-routing panic.

## Static finding

`HirTypeKind` currently declares 27 variants in `src/compiler/20.hir/hir_types.spl`.
`PostMonoVerifier.walk_type` in
`src/compiler/40.mono/verify/post_mono_verify.spl` has an explicit arm for all
27. The AVX fixed vector kinds exist only in MIR, so adding HIR vector match
arms would be incorrect and would not repair the malformed aggregate value.

## Candidate root cause and repair

The native enum matcher accepted only the variant discriminant and ignored the
runtime enum type ID. Two compiler-internal enums with the same variant name
therefore shared a tag and could enter the wrong generated match arm, after
which the payload was decoded using the wrong aggregate layout.

The candidate repair adds `rt_enum_check_variant(value, enum_id, discriminant)`
across the C, pure-Simple, and Rust runtimes. Nonzero IDs must match; ID zero
keeps the legacy user-enum/Result compatibility lane. Pure-Simple top-level and
nested enum-match lowering and the Rust seed HIR/MIR/codegen paths now emit the
identity-aware check. The earlier two-argument ABI remains available.

Focused evidence on 2026-09-09:

- Rust runtime cross-enum collision plus ID-zero compatibility: PASS (1/1).
- Rust HIR-to-MIR `HirTypeKind.Vec16i` versus `MirTypeKind.Vec16i` routing:
  PASS (1/1).
- Pure-Simple runtime/lowering source contract: PASS (3/3).

The original B6 hello-world bootstrap smoke has not been rerun, so the blocker
stays open until the acceptance command below produces zero malformed-type
receipts.

## Required investigation

Trace the `HirType` aggregate across HIR lowering, module storage,
monomorphization cloning/substitution, and the post-mono visitor under the
self-hosted Windows compiler. Capture the raw enum tag before and after each
boundary using a bounded, non-formatting receipt. The fix must preserve the
fail-closed wildcard until the transport boundary producing the invalid tag is
identified and corrected.

## Acceptance

The B6 hello-world frontend smoke completes with zero malformed-type receipts,
and a focused post-mono verifier regression walks primitive, composite,
function, projection, tensor, and layer types without reaching the wildcard.
