# Typed SOURCE instruction rebasing foundation

Status: **source review pending; compiler checks and runtime SSpecs UNRUN**.
This tranche adds pure typed plan rebasing and its data types. It does not
activate dictionary capture, change the request wrapper ABI, or admit a SOURCE
invocation. Full SOURCE C4 and Phase3 acceptance remain open.

The four source files and executable specification are exact blobs from
`06903799e18`, extracted onto observed `release_phase3` base
`e0b15b1f1d49acc71d7ba069d8f10124292196a5`:

- `src/compiler/50.mir/source_region_instruction_rebase_v1.spl`
- `src/compiler/50.mir/source_region_instruction_rebase_types_v1.spl`
- `src/compiler/50.mir/source_region_operation_plan_types_v1.spl`
- `src/compiler/50.mir/source_region_dictionary_site_types_v1.spl`
- `test/01_unit/compiler/source_region_instruction_rebase_v1_spec.spl`

The independent reviewer selected this dependency closure. All other imported
compiler modules are already present in the target. Production caller hooks,
MirLowering state, existing context-positive specifications and default/archive
codecs retain their target versions. The full implementation remains preserved
on `work/c4-caller-source-land-20261026`.

The executable specification asserts six scenarios:

1. Preserve stable original locals when temporary allocations change, and
   rewrite a planned success instruction to the actual local identities.
2. Refuse a prior binding that aliases a stable local.
3. Refuse a stable local whose actual type differs.
4. Refuse an unsupported instruction variant.
5. Refuse an operand without a typed local binding.
6. Validate a structurally matching dictionary-read plan, refuse a changed
   operand and ordinary rebasing of its read debt, preserve a nonempty source
   filename, and refuse an underfunded account for that comparison.

Dictionary-read fixture records are structural inputs, not proof of a live
epoch or retained owner. The pure helper cannot authorize allocation, reading,
retention, or backend emission. No fixture execution, measured coverage,
native resource qualification, or full producer/consumer positive is claimed.
