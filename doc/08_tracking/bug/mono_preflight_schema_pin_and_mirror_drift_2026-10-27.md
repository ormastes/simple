# Mono preflight schema pin stale since v9; mirrors drifted

- Severity: P2
- Status: open
- Owner: mono lane (preflight author 966ee6d04a66)
- Found: hircfg lane, decl-level @cfg step 1 review (Fable), 2026-10-27

## Symptom

`mono_preflight_schema_matches_v1` (`src/compiler/40.mono/mono_invocation_preflight_v1.spl:53`)
pins `spl-hircodec-v8` / `spl-hircodec-canonical-v4` / `spl-flatpool-v7`. The live values are
`v12-cfg-guard` / `canonical-v5-a5-refusal` / `flatpool-v12-field-visibility`. So
`mono_preflight_begin_v1` fails every call with `E-MONO-SCHEMA`, and
`process_modules_checked_v1` (`monomorphize_integration.spl:437`) refuses every module.
`test/01_unit/compiler/mono/mono_invocation_preflight_v1_spec.spl` is red on every case (12 cases).

## History

- 2026-10-21 03:10: pin written (966ee6d04a66). It matched v8 at that time.
- 2026-10-21 16:27: codec v9 + canonical-v5 (1946088e309). Neither the pin nor the mirrors were updated.
- 2026-10-23: v10, 2026-10-25: v11, 2026-10-27: v12 (decl step 1). These did not update the pin either.

## Why the pin was not simply updated

The pin exists to stop a stale `mono_preflight_visit_*` mirror from being admitted.
Updating it to v12 (tried, then reverted) turns 8/13 cases green and leaves 5 red. Those 5
show real copy_units drift in the type, dict and module-key walks:

    admits open generic composite type and effect evidence before specialization: expected 173 to equal 0
    accepts the exact measured work bound and refuses one less: expected 43 to equal 0
    traverses empty dictionaries and populated text indexes without mutating input: expected 130 to equal 0
    admits exact dictionary traversal work and refuses a smaller allowance: expected 142 to equal 0
    refuses an absent required function key before looking up its declaration: expected "" to contain E-MONO-SHAPE

Flipping the pin while those mirrors are short would be the false-green the gate exists to prevent.

## Expected fix

Bring every `mono_preflight_visit_*_v1` mirror up to the v12 codec layout. HirFunction (cfg,
cfg_group, cfg_arm) and FunctionAttr (is_inline, is_comdat_instance) are already mirrored by
decl step 1. Then update the pin, and add this case to the spec:

    it "charges HirFunction cfg entries exactly like the codec":
        guarded.cfg = ["a", "b"]  # delta vs cfg=[] must be 2 + 2*2 copy_units

Also consider a generator-produced mirror, or a freshness check, so codec bumps cannot leave
the mirror stale again.
