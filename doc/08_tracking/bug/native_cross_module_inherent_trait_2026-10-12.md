# Native cross-module inherent trait implementation is unsupported

Status: OPEN / UNSUPPORTED. Scope: Rust bootstrap native-project per-file
compilation, Cranelift, and flattened module-loader composition. This is
separate from importing a trait alias for a local implementation and from
same-file separate inherent methods.

## Reproducer and expected behavior

`test/fixtures/compiler/implicit_trait_alias/device.spl` declares
`Device(AliasProbe)` with no inline methods. Its consumer imports `Device as
Alias`, supplies `impl Alias.read`, and invokes `read` through `AliasProbe`.
The desired result is 37 and `IMPLICIT_TRAIT_ALIAS_PASS value=37`, exit 0.
The positive fixture retains that future oracle; its header documents the
current limitation. Its `assert` call also encounters the separately tracked
[native assert ABI bug](native_callable_assert_platform_alias_2026-10-12.md).

## Retained execution evidence

- Old source `3e6da6a19a3a3ad0f11e2d6419dcd1dcdc06d5ba`, retained Rust bootstrap
  producer/runtime: two files compiled, exit 0; executable exited 139.
  Both compile and run watchdogs reported complete and quiescent.
- Diagnostic output: `/root/simple-alias-oldproducer-diagnostic-c0qpmgcj`.
  `inputs.json` pins source, producer, archive, original fixture and diagnostic
  fixture hashes; logs, receipts, symbols and disassembly remain there.
  Only the copied assertion was changed to an equivalent explicit failing
  return to avoid the independent assert ABI bug. Original fixtures were
  preserved. Binary SHA256:
  `5bd503dd501ef477bf55b2305efbe7c76aeeefaede8b0c5a65570187121a0ad3`.
- Baseline disassembly: `spl_main` allocates zero bytes without a vtable store;
  `through_alias` dereferences the receiver header and slot zero. The executable
  has no vtable symbols. This case was already unsafe before the new check.
- New source `0596863c905a26566072da7c5f165a8dc20d130d`: native compilation
  refuses `device.spl`, exit 1, with `Unsupported feature: implicit trait
  implementation AliasProbe for Device lacks required method read`.
  Original failed positive row remains at
  `/root/simple-block-next-regression-zpqdp5cv/alias`; it is not a PASS.
- The original flattened positive test
  `implicit_trait_import_alias_matches_emitted_inherent_symbol` also FAILED:
  `/root/simple-block-repair-canonical-next-20261012/rust-structural-tests/implicit_trait.log`
  records six passing tests and this one failure at `unwrap`, with
  `Unsupported("implicit trait implementation Probe for Device lacks required method read")`.
  This disproves the earlier assumption that the flattened path supported the
  cross-module extension. That original failed receipt is preserved unchanged.
  Its replacement, `implicit_trait_cross_module_extension_refuses_incomplete_table`,
  retains identical source inputs and asserts the exact safe-refusal diagnostic.
  The new negative test is authored, not yet executed; it is not a retroactive
  PASS for the original positive test.

## Cause and repair boundary

Per-file implicit implementation synthesis cannot see inherent methods defined
in the importing consumer. The native project's shared import inventory does
not provide a complete, declaration-owner-bound implementation table for this
case. In addition, `codegen/common_backend.rs::emit_vtable_data_objects` leaves
an unresolved cross-module function slot zero. Supplying a symbol string or
removing the required-method check alone would not repair executable dispatch.

A future repair must bind complete implementation inventory to the canonical
declaration path/name, preserve actual emitted symbols and receiver/parameter
ABI, declare external function relocations, and keep constructor/header layout
consistent. Missing or ambiguous required methods must still refuse safely.

## Required qualification

The supported scoped requirement is importing a trait alias while defining its
concrete type and separate inherent implementation locally. The passing
`implicit_trait_per_file_import_keeps_selected_required_and_default_methods`
test covers that path, including a later unrelated same-name trait, retained
defaults and a missing-required negative. This does not establish cross-module
inherent extension support.

For cross-module support, compile and execute this positive fixture through an admitted
matching producer/runtime, retaining the original assertion and marker. Cover
same-name foreign owners, alias substitution, duplicate methods, defaults and
truly missing required methods. Until then, a separately named compile-negative
test may verify the exact safe refusal, but must report support as UNSUPPORTED
and must not replace or relabel the original failed positive result.
