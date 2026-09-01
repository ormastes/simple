# AC-12 BootstrapSdk Capsule Source Contract

**Executable spec:** `test/03_system/compiler/bootstrap_sdk_capsule_source_contract_spec.spl`

## Purpose

This is a source-contract guard for the future provenance-bound Bootstrap SDK
capsule. The authoritative plan says execution is gated on an exact x86_64
Stage 4 candidate. It names the future manifest, module-interface, body-archive,
and provenance records, including their required identity and hash fields. The
existing SHB interface/dependency surfaces are starting seams only; they are not
accepted as sufficient capsule authority.

## Checked source facts

The executable spec verifies the plan's exact frozen-contract wording and the
current `ShbModuleInterface`, dependency reader, extractor, and deterministic
interface-hash seams. It also records two blocking SHB gaps deliberately:

- `extract_dependency` emits `ShbDependencyEntry.interface_hash: 0`, so direct
  dependency interfaces are not currently bound; and
- `shb_canonical_api_string` has no `iface.dependencies` contribution, while
  `ShbEnumEntry.variants: [text]` and the extractor retain enum names without
  payload-type closure.

These are source facts, not passing capsule behavior. When the capsule work
implements either gap, this transitional source assertion must be replaced by
the corresponding executable admission evidence.

The final scenario preserves the plan's current boundary: no capsule outcome may
change state to `pass` before the x86 candidate is admitted, and an opt-in must
not claim capsule success by falling back to a stale capsule, raw source, or the
Rust seed. The current bootstrap entrypoint is checked only for its existing
`--fresh-cache`/bootstrap seam.

## Limits

This does **not** claim that a Bootstrap SDK capsule currently exists, can be
written or loaded, rebuilds any compiler, or proves runtime bootstrap behavior.
Those claims remain blocked until the planned writer, reader, admission,
two-generation, reproducibility, and exact-binary evidence gates are
implemented and exercised.
