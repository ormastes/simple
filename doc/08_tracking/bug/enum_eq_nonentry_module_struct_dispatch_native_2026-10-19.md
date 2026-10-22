# Enum `==` in a NON-entry module lowers to struct `__eq__` dispatch natively (2026-10-19)

## Status: RESOLVED by r16b (no longer reproduces natively); most likely fix 669c103e90a (unproven)

## Symptom

r13 Stage 2 (`e6cb4bfd5533a790`, aarch64, `--threads 1`), three modules:

- `src/lib/common/zz_natfront_probe/model.spl`: `pub enum Kind: PureSimple | Other`
- `test/zz_natfront_probe/p3b8/consumer.spl`: `use std.common.zz_natfront_probe.model.{Kind}`,
  `pub struct LocalProv(kind: Kind, flag: bool)`, `pub fn prov_ok(p)` with
  `if p.kind != Kind.PureSimple or not p.flag` (consumer.spl:8:8)
- `test/zz_natfront_probe/p3b8/main.spl`: imports both, calls `prov_ok`.

```
MIR lowering error: unresolved method call: operator overload for struct
lib.common.zz_natfront_probe.model.Kind (no matching __add__/.../__eq__/...)
at .../test/zz_natfront_probe/p3b8/consumer.spl:8:8
```

The same compare in the ENTRY module (probe p3b7) builds and runs. Real-code
instance: `lib.common.rt_hal.model.RtHalProviderKind` /
`RtHalOperationKind` compared inside `std.nogc_sync_mut.rt_hal.parallel_executor`
(probe p3b6, 6 sites).

## What was tested

| experiment | result |
|---|---|
| default build (HIR shard worker encodes, parent decodes via `hir_codec`) | 2 errors |
| `SIMPLE_HIR_CACHE=0` (zero HIR shards, in-process HIR, no codec), clean tree | **2 errors** |
| in-process harness, 3 modules, one shared `MirLowering`, prescan all, lower entry first (`enum_field_eq_lowering_spec.spl`) | green |
| same, enum module keyed `lib.common.zz.model` imported as `std.common.zz.model` | green |
| same, prescan order entry -> consumer -> model | green |

So the suspected cause — dependency HIR losing enum information through the
shard-cache codec — is **ruled out** by the second row: the defect reproduces
with no shard and no codec. (Separately: the codec cannot be exercised by the
deployed aarch64 test runtime at all — `hir_module_encode` calls
`rt_heap_ref_registered`, unknown to that runtime; the pre-existing
`test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl` is red 1/4 for the
same reason.)

## Evidence from the shard HIR blobs (run B, text codec)

- Consumer table: imported `Kind` is SymbolKind 7 (Enum),
  `defining_module = lib.common.zz_natfront_probe.model`. Entry table: same,
  twice (direct import + transitive through `app.consumer`).
- Enum registry at consumer lowering time: `q_registry=3` (model's `Kind`
  registered under `lib.common.zz_natfront_probe.model.Kind`, which is also
  the name the error prints) — `SIMPLE_ENUM_REG_TRACE=1`.
- Native `HirModule.name` is the absolute SCV snapshot PATH. For the
  `test/...` modules `module_logical_name_from_path` does not find a repo
  root and yields a mangled `.home.yoon.dev.simple_lane_natfront.build.scv.snapshots.<rev>.test.zz_natfront_probe.p3b8.consumer`;
  the `src/lib` module yields the clean `lib.common.zz_natfront_probe.model`.
- The entry's HIR module carries a materialized copy of `LocalProv`
  (`defining_module` = the consumer's snapshot path) whose field type refers
  to ENTRY-local symbol ids; the native driver prescans the entry first, so
  the NAME-keyed `struct_field_hir_type["LocalProv"]` /
  `struct_field_type_ownership_key` rows are first-wins filled from that copy
  (`prescan_module_struct_names`, module_lowering.spl:1704, "first module
  wins on a name collision"). The in-process harness's
  `module_surfaces_from_modules` does not materialize such a copy, which is
  the one native/harness differential left standing.

## Where to look next

`declared_field_type_in_current_table` (expr_dispatch.spl:894) rebinding the
entry-copy's `Named(entry_id)` into the consumer's table by ownership key,
and the owner-key spelling when the owner's `defining_module` is a snapshot
path that `hir_symbol_owner_module` cannot make repo-relative. A harness row
needs the entry's materialized import copy (as `module_reexport_materialization`
produces under `--entry-closure`) to go red; the r13 compiler is prebuilt, so
a `src/compiler` fix can only be verified through such a row.

## Guard spec

`test/01_unit/compiler/50.mir/enum_field_eq_lowering_spec.spl` was calling the
stale one-arg `prescan_module_struct_names(hir)` and failed before reaching
MIR. It now uses the `(Dict<text, HirModule>, key)` API and pins the 3-module,
shared-lowering, entry-first, `std.`-imported shape — green, i.e. it does
**not** capture this defect; it is the de-staled regression guard for the
original 2-module incident only.

Probes: scratchpad `natfront/probes_saved/{lib_model,p3b8,p3b7,p3b6}`; runs
`natfront/p3b8_{A2,B,T}`.

## Resolution (2026-10-20)

Same worktree (`1919f812dfe`), same flags (`--threads 1`, MemoryMax=4G):

| compiler | p3b8 (probe enum in src/lib) | `test/fixtures/native_enum_eq_nonentry` | p3b6 (rt_hal) |
|---|---|---|---|
| r13 Stage 2 `e6cb4bfd5533a790` (source `200225109265`) | **red** (`operator overload for struct lib.common.zz_natfront_probe.model.Kind`) | **red** (`... lib.common.rt_hal.model.RtHalProviderKind`) | red (doc above) |
| r16b Stage 2 `645e62a815d076d7` (source `ed5406ed760`) | green, `ok true` / `other false` | green, `ok true` / `other false` | green, `err=[]` |
| r16b, `SIMPLE_MIR_EAGER_PROVIDER_LAYOUTS=1` | green | — | — |

The eager-layout row rules out the demand-layout change (`cc601e8f3d3`).
The most likely fix in the 147 MIR/HIR/driver commits between the two
sources is `669c103e90a` ("rebind declared field type for field-chain method
receivers"): before it, `declared_field_hir_type` returned the bare-name
prescan row's field `HirType` raw, i.e. a `Named(id)` from the DEFINING (or
the entry copy's) symbol table read in the importer's table — the exact
id-space confusion recorded above. That attribution is NOT proven: a
per-commit native bisect needs a Stage 2 per commit.

**The in-process harness does not reproduce it, even on the r13 source.**
Measured on a `200225109265` worktree: swapped entry imports, padded consumer,
and an injected entry-side materialized `LocalProv` copy whose `Kind` id
differs from the consumer's — all green. A test-local enum module is also
green natively on r13; the failure needs the enum in `src/lib` imported as
`std.` (the snapshot-path vs `lib.` owner spelling).

**Guards:**
- Native (discriminating): `test/fixtures/native_enum_eq_nonentry/` —
  red on r13, green on r16b. Uses the real `std.common.rt_hal.model`
  enum so no probe module is added to `src/lib`.
- In-process: `enum_field_eq_lowering_spec.spl` gains the materialized-copy
  row (6/6 green). It hardens the lowering against that HIR shape but, as
  measured above, does not go red on r13.
