# Gen2 Raw Artifact Writer Can Pair Valid Provenance with Arbitrary VHDL

Status: exported bypass removed; language-level authority remains unresolved

## Observation

`src/compiler/80.driver/driver_vhdl_artifacts.spl` exposes the generic
`vhdl_render_production_artifacts(input, vhdl)` and
`vhdl_write_production_artifacts(output, vhdl, rendered)` helpers. A
well-formed `VhdlArtifactInput` for an `hwir-gen2-*` route passes its typed
metadata validation, while the generic renderer accepts arbitrary VHDL text and
the writer has no access to the originating graph or route.

The normal Gen2 driver recomputes and compares graph identity before it calls
its private authorization/render/write helpers. The generic raw writer rejects
all three compiler-owned Gen2 routes before stale-artifact cleanup, and the
former exported `vhdl_write_compiler_gen2_production_artifacts` bypass has been
removed. The raw protocol rejects a Gen2-shaped manifest paired with forged
VHDL and preserves existing files on rejection.

Residual: the receipt and its writer are private by module convention only.
Simple visibility checking is warn-only and does not enforce constructor or
field access, while `VhdlArtifactInput` and rendered values remain serializable
for generic artifact APIs. This narrows the supported/public API surface; it
does not establish a language-enforced, cryptographic, or capability-enforced
authority over Gen2 VHDL provenance.

## Safety impact

An artifact manifest must not attest to a compiler-owned typed HWIR product
unless its VHDL was regenerated from that exact product closure. This is a
provenance-integrity gap, not evidence of a current generated RTL defect.

## Required remediation

1. Completed: reject every `hwir-gen2-product`, `hwir-gen2-stateful-product`,
   and `hwir-gen2-trap-stateful-product` route in the generic raw write
   protocol before stale-artifact cleanup.
2. Completed at the exported API boundary: the Gen2-only write path now lives
   with the product driver behind a private receipt; no artifact-module export
   accepts serializable Gen2 input plus raw VHDL.
3. Preserve the generic catalog and `hwir-strict` artifact path.
4. For true non-forgeability, make cross-module private access, constructors,
   and field writes hard compiler errors, then add a negative compile test for
   manufacturing the receipt outside its owner module.
5. Retain regression coverage for raw Gen2 rejection/preservation and
   RV32/RV64 canonical product acceptance.

## Unblock evidence

Run the focused artifact-manifest and Gen2 driver specs with the admitted
self-hosted runtime, then retain an RV32/RV64 critical CLI manifest/VHDL/GHDL
receipt. Do not make a mission-critical release claim that depends on
language-level non-forgeability until remediation item 4 is complete.

Owner: RISC-V Gen2 compiler-product provenance lane
