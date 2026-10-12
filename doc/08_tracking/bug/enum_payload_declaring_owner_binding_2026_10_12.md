# Enum payload types lose the declaring owner namespace

Status: focused HIR repair verified; full qualification remains OPEN.

## Evidence

The Phase 3 aggregate cycle 3 reported 396 HIR errors across 21 owners and
produced no object/archive. Its three-attempt budget remains exhausted.
This repair does not authorize another aggregate build.

A separate bounded single-entry compile of
`compiler/70.backend/backend/verification_codegen_types.spl`, using the
qualified generic Phase 2 producer, reproduced `unresolved type: MirType`.
The closure has 148 modules; it timed out after 120 seconds after retaining
the target failure. No object was produced. Diagnostic trace identifies
`compiler.mir.mir_instruction_kinds` and `compiler.mir.mir_instruction_support`
as the declaring owners passed to payload projection. The former already has
explicit imports of `LocalId`, `MirType`, and `MirSignature` from `mir_types`.
Adding imports to consumers therefore does not repair this owner boundary.

Local evidence: `/mnt/c/Temp/simple-phase3-owner-projection-repair-20261012/`;
`owner-projection-diagnosis.json` retains the failure samples and projection
miss counts. The original aggregate receipt remains authoritative for its
396 errors; this probe is neither a replacement aggregate nor admission.

## Root cause and proposed repair

`register_materialized_payload_named_dependency_inner` resolves the physical
terminal and registers its type. It never publishes the dependency spelling
in the enum declaring module's qualified type table. `lower_variant` passes
that declaring module to `imported_surface_type`; the qualified lookup misses
and falls back to the importing module's short-name namespace.

The callable-dependency sibling already binds terminal and declaring-owner
identities. The candidate applies that same second binding to enum payloads,
before the expanded-origin early return. This preserves renamed imports and
multiple enum owners referring to an already expanded canonical type.

Workaround tag: `ENUM_PAYLOAD_OWNER_SCOPE_FALLBACK` identifies reliance on the
consumer accidentally importing the payload type. The proposed compiler fix
removes that dependency; no synthetic type aliases or consumer exclusions are
introduced. It is platform-neutral HIR logic, but Windows/macOS/BSD/SimpleOS
execution is unverified.

## Prevention and limits

`enum_payload_qualified_owner_binding_spec.spl` checks actual HIR symbol IDs
for two declaring owners and for a renamed import after terminal expansion.
It is a semantic test, not a source-string assertion. It has not been executed
with the rebuilt producer: this bootstrap CLI does not include the SSpec runner.

Small native hidden-field and enum alias fixtures compiled successfully.
A collision fixture also linked against the generated core-C runtime and
passed one real assertion while retaining the missing-owner projection trace.
Those results show that incidental short-name bindings can mask the defect;
they do not prove the candidate repair. No claim that all 396 failures share
this cause is made.

## Bounded native qualification

The reviewed body-only repair was rebuilt from immutable qualified Phase 2
source (990bd78f plus namespace b316 and generic 181eb49); no unrelated release
source was overlaid. The 445c seed reused 1,234 modules and rebuilt exactly the
entry, mandatory assembly parser, and changed HIR owner. Compile exit 0,
52.30 seconds, peak process-tree RSS 1,574,404,096 bytes. Source identities were
unchanged during compilation.

Successor SHA-256: `b20ad174493ac6a18207c0c3b4aa717cb9a7d4455f80f7a9b18f5c515f1d3d60`.
It links the unchanged Rust producer runtime cc2840/eb46 and SOSIX directory
projection. It compiled Hello; that output linked against the generated core-C
47a386/935f72 target runtime and ran `HELLO_ENUM_PAYLOAD_OWNER`, exit 0.

The real failing `verification_codegen_types` module then completed HIR
lowering with succeeded=1, failed=0 (32.103 seconds into the focused run).
Its prior MirType owner-projection misses disappeared. The remaining
148-module dependency/object result is retained separately in
`focused-candidate-receipt.json`; this owner criterion does not establish that
all 396 aggregate errors are repaired.

The focused candidate completed HIR for all 148 dependency modules with zero
failures, but the object attempt was stopped at its explicit 300-second limit:
exit -9, peak tree RSS 1,986,396,160 bytes, object bytes 0. MIR emitted unresolved
method calls lowered to const-0 placeholders, so no native closure behavior or
admission is claimed. The owner HIR criterion is complete and must not be
rerun without new changes; the downstream MIR boundary remains separate.
