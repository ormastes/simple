# RC1 recursive facade item projection

## Reproducer and evidence

The admitted Stage 2 producer fails the 87-source native closure rooted at
`src/app/compiler_schema/main.spl`: 13 poisoned modules and 20 HIR errors.
Four generators explicitly import `dir_create_all` from `std.io_runtime` but
their call sites report it unresolved.

The bounded diagnostic run enabled `SIMPLE_BOOTSTRAP_DIAG=1` and
`SIMPLE_REXMEMO_VERIFY=1`, retained normal streaming surfaces and disabled stub
fallback. It terminated with exit 1. Local evidence is
`build/native_probe/config-layout/facade-resolution-schema.log`.

Lines 3928–3930 distinguish the lookup result from its recursive consumer:

- The facade hop finds `dir_create_all` in physical surface 13,
  `nogc_sync_mut.io_runtime`; that surface declares the item.
- The facade reports `found=true`.
- The immediate terminal registration searches for the item
  `nogc_sync_mut.io_runtime`, the module spelling, instead of `dir_create_all`.

The same corruption affects `read_file_text`, `file_exists`, and `file_write`
in the adjacent trace. No root memo mismatch or invalid registry diagnostic
was emitted. This evidence identifies loss of item identity across the native
recursive registration boundary; it does not establish the lower-level
code-generation defect responsible for the projection-slot aliasing.

## Candidate repair

Project the returned re-export carrier into local scalar values before
diagnostic calls or another surface projection. Resolve the registry name in
a separate statement and pass both scalar spellings to recursive registration.
Keep the item scalar for the qualified-type lookup afterward. Apply the same
item snapshot at the two enum-payload origin consumers that read another
surface before consuming the item.

This changes no route precedence, cache lifetime, visibility, or error policy,
and adds no scans or retained caches. The underlying native projection/codegen
bug remains a follow-up investigation; no global cache disabling or direct
extern replacement is introduced.

## Verification status

- `git diff --check`: PASS.
- Added executable SSpec in `reexport_physical_cache_spec.spl`: register a
  facade item under an alias, assert its qualified terminal identity and the
  absence of a module-name binding, then register a second alias through the
  cached root.
- Rebuilt producer, SSpec execution, and the 87-source reproducer after the
  repair: pending the parent's combined Stage 2 build. No runtime PASS claimed.

**STATUS: WARN — candidate repair awaiting rebuilt-producer evidence.**

## First rebuilt producer: actual field-offset defect

The first combined rebuilt producer
`build/phase_snapshots/phase1_1790649469_phase2_1790650801/simple`
still misregisters the same names. Its diagnostic closure has 17 errors;
the three generic-template failures disappeared independently. Snapshotting
scalars alone did not fix this bug.

Static LLDB disassembly of `HirLowering.find_reexport_source` shows the precise
layout mismatch. The memo-hit constructor writes its four-word result with
`module_name` at offset `0x10` and `item_name` at `0x18`
(instructions `0x100132b40`, `0x100132b4c`). But the fresh walk's inferred
`result.item_name` is read from offset `0x10` when publishing the memo
(`0x100132950`), and `result.found` is also read from offset `0x10`
(`0x100132708`) instead of zero. These are incorrect nominal field offsets,
not evidence of a transient lifetime problem. Saved disassembly:
`build/native_probe/config-layout/facade-cycle1-root-address-disassembly.txt`.

The next candidate explicitly annotates all returned `HirReexportSource`
carriers at this route boundary, including recursive walk, memo publication,
verification, dependency candidates, and terminal registration. The defining
module is imported explicitly. The adjacent export-origin lookup and walk
state carriers also retain their declared nominal types. Scalar snapshots
remain, but are insufficient without correct field typing.

The native inference bug itself remains open: an inferred method return
carrier must never select another aggregate's field layout. This bounded
repair preserves the intended source type while the underlying inference
owner is investigated. Second rebuilt-producer execution is pending; no
runtime PASS is claimed for these annotations.
