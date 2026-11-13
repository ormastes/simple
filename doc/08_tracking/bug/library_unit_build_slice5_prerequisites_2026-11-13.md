# Library unit build: two prerequisites before Stage 3 links from unit archives

**Status:** OPEN (recorded 2026-11-13). **Lane:** `work/lib-link-units-20261113`.
**Design:** `doc/05_design/compiler/incremental_build/library_unit_build_and_link.md`.

Slices 1-4 and the pure half of slice 5 are landed as unwired functions
(`driver_build/library_unit_{plan,iface,archive,graph,link}_v1.spl`). Turning
`SIMPLE_NATIVE_LIBRARY_UNITS=1` / `--library-units` on in `native-build` is
blocked on two compiler-side facts, neither of which any digest can paper over.

## 1. Unit-scoped lowering does not exist

`lower_to_mir_with_target_context` lowers module M with `providers = all of
ctx.mir_feed_modules` (the whole closure) plus whole-closure prescans
(`mir_shard_export_summaries.md` §"What MIR lowering of module M reads").
Building a unit ONCE requires lowering its modules against its dependencies'
**interface artifacts only** (`iface.sdn` + the body-free declaration carrier),
never against their HIR. The MIR shard export summary (`driver_mir_shard_export_v1`)
is the intended body-free carrier for rows 1-19 and is the thing to feed a
unit build instead of provider HIR. Until that path exists, a "unit build" is
just the whole-closure build with its objects filed per unit — correct, but it
reuses nothing.

## 2. Row 22: order-dependent counters

`canonical_type_symbols` (`module_lowering.spl:832`) and `mcdc_next_runtime_id`
(`mir_lowering_types.spl:116`) take values from whole-closure lowering ORDER.
Two units lowered in separate processes can collide or disagree. Needed: derive
them from symbol identity (deterministic per unit) or record them in
`receipt.sdn` and refuse a link whose units disagree. Verification: lower the
same unit in two processes with different sibling sets; objects must be
byte-identical.

## Also stated in the design, not blockers

- Static archives dead-strip unreferenced members (registration tables, extern
  registries, static initialisers). Stage 3 links the receipts' object lists
  (or `--whole-archive`) until a unit is proven safe for selective linking.
- Generic monomorphization is NOT a leak in the default erased lane; under the
  `40.mono` archive lane cross-unit instances come from the pre-link instance
  lane, never from a unit archive.
- Symlinked sources are unaddressed (planning and digests are pure text).

## Verification that exists today

Specs under `test/01_unit/compiler/80.driver/library_unit_*_spec.spl` (plan 18,
iface 14, archive 8, graph 6, link 7) on the Rust bootstrap seed; the iface spec
proves struct field reorder, enum variant insert AND reorder, `val` value,
multi-line `"""` string-constant body (review M1 fix in `native_interface_decls_v1`)
and method default changes each change the unit interface digest while
fn/method bodies and module docstrings do not. Unit archives require llvm-ar
(`library_unit_archiver_v1`), never binutils `ar`.
