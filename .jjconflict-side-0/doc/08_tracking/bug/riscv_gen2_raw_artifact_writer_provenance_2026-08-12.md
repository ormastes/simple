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

## Re-verification 2026-08-17 (content-based, lane w03/C)

The triage row for this doc read: *"Doc claims 'exported bypass removed' but
lines 922-924 still `export` both helpers."* **That triage note is a misreading
of the doc, and the doc is correct as written.** Recorded here so the next sweep
does not re-open this on the same false signal.

The "exported bypass" this doc claims to have removed is the distinct symbol
`vhdl_write_compiler_gen2_production_artifacts` — a Gen2-specific writer that
took serializable Gen2 input plus raw VHDL. Verified against current source:

- `grep -rn vhdl_write_compiler_gen2_production_artifacts src/compiler/ test/`
  returns **three hits, all of them negative assertions** in
  `test/01_unit/compiler/backend/vhdl_artifact_manifest_spec.spl:557-563`, which
  assert the symbol is absent from both the artifact module and the driver.
  Zero hits anywhere in `src/`. The bypass is genuinely gone, and its removal is
  regression-pinned.

The two helpers still exported at `driver_vhdl_artifacts.spl:922` and `:924`
(`vhdl_render_production_artifacts`, `vhdl_write_production_artifacts`) are the
GENERIC source-owned path, which the doc never claimed to unexport. They are
guarded rather than withdrawn:

- `vhdl_write_production_artifacts` (`:904`) rejects all three compiler-owned
  Gen2 routes at `:913-915`, via `vhdl_rendered_claims_compiler_owned_gen2`
  (`:857`, manifest route marker) OR `vhdl_text_claims_compiler_owned_gen2`
  (`:870`, raw VHDL route marker) — the second closing the forged-payload hole
  where a legacy manifest carries a Gen2 marker in the VHDL. The rejection
  returns before `vhdl_write_artifacts_after_authorization` (`:884`), so
  stale-artifact cleanup never runs on a rejected bypass and existing files are
  preserved, exactly as the doc states.
- `vhdl_render_production_artifacts` (`:806`) is a pure renderer with no I/O, and
  it hard-codes `"qualification":{"status":"FAIL","reason":
  "unqualified_generated_artifact"}` at `:841`. It therefore cannot mint a
  qualified receipt for arbitrary VHDL; every manifest it produces is
  self-declared unqualified.

**Status unchanged and correct: the exported bypass is removed; the residual is
the language-level authority gap already recorded above (remediation item 4 —
cross-module private access, constructors and field writes are warn-only, so the
receipt is private by module convention, not by enforcement).** No code change
made in this sweep; there is no silent-wrong-result defect here to fix, and the
remaining item is a visibility-enforcement feature in the type system, not a
defect in this file.

Classification for this sweep: **already-fixed as filed; triage verdict was a
false positive.**
