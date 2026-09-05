# Storage Projection Registry Specification

> Tests covering driver-owned storage projection registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Projection Registry Specification

## Scenarios

### driver-owned storage projection registry

#### keeps repeated MIR local identities isolated by module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps repeated MIR local identities isolated by module


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps repeated MIR local identities isolated by module")
val ctx = CompileContext.create(driver_core_compile_options_default())
assert_true(ctx.storage_binding_rows_well_formed())
assert_equal(ctx.storage_view_site_bindings_for_module("particles").len(), 0)
assert_equal(ctx.register_storage_view_site_binding("particles",
    registry_site(StorageLayoutKind.SoA, 7, 64)), "ok")
assert_equal(ctx.register_storage_view_site_binding("other",
    registry_site(StorageLayoutKind.AoS, 9, 0)), "ok")
val particles = ctx.storage_view_site_bindings_for_module("particles")
val other = ctx.storage_view_site_bindings_for_module("other")
assert_equal(particles.len(), 1)
assert_equal(other.len(), 1)
assert_equal(particles[0].binding.revision, 7)
assert_true(particles[0].binding.plan.layout == StorageLayoutKind.SoA)
assert_true(other[0].binding.plan.layout == StorageLayoutKind.AoS)
```

</details>

#### rejects duplicate sites without partially mutating aligned rows

- rejects duplicate sites without partially mutating aligned rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects duplicate sites without partially mutating aligned rows")
val ctx = CompileContext.create(driver_core_compile_options_default())
val site = registry_site(StorageLayoutKind.SoA, 7, 64)
assert_equal(ctx.register_storage_view_site_binding("particles", site), "ok")
assert_equal(ctx.register_storage_view_site_binding("particles", site),
    "duplicate-storage-view-site-binding")
assert_equal(ctx.storage_binding_module_names.len(), 1)
assert_equal(ctx.storage_view_site_bindings.len(), 1)
assert_true(ctx.storage_binding_rows_well_formed())
```

</details>

#### builds registration-order-independent cache identity and evicts by module

- builds registration-order-independent cache identity and evicts by module


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds registration-order-independent cache identity and evicts by module")
val first = CompileContext.create(driver_core_compile_options_default())
val second = CompileContext.create(driver_core_compile_options_default())
val particles = registry_site(StorageLayoutKind.SoA, 7, 64)
val other = registry_site(StorageLayoutKind.AoS, 9, 0)
_ = first.register_storage_view_site_binding("particles", particles)
_ = first.register_storage_view_site_binding("other", other)
_ = second.register_storage_view_site_binding("other", other)
_ = second.register_storage_view_site_binding("particles", particles)
assert_equal(first.storage_binding_identity(), second.storage_binding_identity())
val changed = CompileContext.create(driver_core_compile_options_default())
_ = changed.register_storage_view_site_binding("particles",
    registry_site(StorageLayoutKind.SoA, 8, 96))
assert_false(first.storage_binding_identity() == changed.storage_binding_identity())
first.evict_mir_module("particles")
assert_equal(first.storage_view_site_bindings_for_module("particles").len(), 0)
assert_equal(first.storage_view_site_bindings_for_module("other").len(), 1)
```

</details>

#### registers full evidence atomically and freezes one immutable identity

- registers full evidence atomically and freezes one immutable identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registers full evidence atomically and freezes one immutable identity")
val ctx = CompileContext.create(driver_core_compile_options_default())
val first = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
val duplicate = registry_evidence(StorageLayoutKind.AoS, 9, 0,
    "allocation:b", "snapshot:b")
# Duplicate site inside one batch must not append the first row.
assert_equal(ctx.register_storage_view_evidence_batch("particles",
    [first, duplicate]), "duplicate-storage-view-site-binding")
assert_equal(ctx.storage_view_evidence_rows.len(), 0)
assert_equal(ctx.storage_view_site_bindings.len(), 0)
assert_equal(ctx.register_storage_view_evidence_batch("particles", [first]), "ok")
assert_true(ctx.storage_registry_rows_well_formed())
assert_equal(ctx.storage_view_evidence_for_module("particles").len(), 1)
val frozen = ctx.freeze_storage_registry()
assert_true(frozen.starts_with("frozen:"))
assert_equal(ctx.freeze_storage_registry(), frozen)
assert_equal(ctx.storage_binding_identity(), frozen)
assert_equal(ctx.register_storage_view_evidence_batch("other", [first]),
    "storage-registry-frozen")
ctx.evict_mir_module("particles")
assert_equal(ctx.storage_binding_identity(), frozen)
assert_equal(ctx.storage_view_evidence_for_module("particles").len(), 1)
```

</details>

#### includes full producer evidence in registration-order-independent identity

- includes full producer evidence in registration-order-independent identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("includes full producer evidence in registration-order-independent identity")
val first = CompileContext.create(driver_core_compile_options_default())
val second = CompileContext.create(driver_core_compile_options_default())
val row_a = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
val row_b = MirTypedStorageViewEvidenceV1(..registry_evidence(
    StorageLayoutKind.AoS, 9, 0, "allocation:b", "snapshot:b"),
    site: mir_storage_view_site_binding_v1(42, 1, true,
        registry_site(StorageLayoutKind.AoS, 9, 0).binding))
_ = first.register_storage_view_evidence_batch("a", [row_a])
_ = first.register_storage_view_evidence_batch("b", [row_b])
_ = second.register_storage_view_evidence_batch("b", [row_b])
_ = second.register_storage_view_evidence_batch("a", [row_a])
assert_equal(first.freeze_storage_registry(), second.freeze_storage_registry())
val changed = CompileContext.create(driver_core_compile_options_default())
_ = changed.register_storage_view_evidence_batch("a", [
    MirTypedStorageViewEvidenceV1(..row_a, source_revision: "snapshot:changed")
])
assert_false(first.storage_binding_identity() == changed.freeze_storage_registry())
```

</details>

#### fails freeze when legacy site rows have no matching evidence

- fails freeze when legacy site rows have no matching evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails freeze when legacy site rows have no matching evidence")
val ctx = CompileContext.create(driver_core_compile_options_default())
assert_equal(ctx.register_storage_view_site_binding("legacy",
    registry_site(StorageLayoutKind.SoA, 7, 64)), "ok")
assert_false(ctx.storage_registry_rows_well_formed())
assert_equal(ctx.freeze_storage_registry(), "invalid")
```

</details>

#### installs produced MIR and full evidence as one driver transaction

- installs produced MIR and full evidence as one driver transaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("installs produced MIR and full evidence as one driver transaction")
val ctx = CompileContext.create(driver_core_compile_options_default())
val original = MirModule(name: "original", functions: {}, statics: {},
    constants: {}, types: {})
val rewritten = MirModule(name: "rewritten", functions: {}, statics: {},
    constants: {}, types: {})
ctx.mir_modules["particles"] = original
val row = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
val failed = MirTypedStorageViewProducerResultV1(ok: false,
    module: rewritten, sites: [], evidence: [], produced_count: 0,
    reason: "sabotage")
assert_equal(ctx.install_produced_storage_module("particles", failed),
    "typed-storage-producer:sabotage")
assert_equal(ctx.mir_modules["particles"].name, "original")
assert_equal(ctx.storage_view_evidence_rows.len(), 0)
val produced = MirTypedStorageViewProducerResultV1(ok: true,
    module: rewritten, sites: [row.site], evidence: [row],
    produced_count: 1, reason: "ok")
assert_equal(ctx.install_produced_storage_module("particles", produced), "ok")
assert_equal(ctx.mir_modules["particles"].name, "rewritten")
assert_equal(ctx.storage_view_evidence_for_module("particles").len(), 1)
```

</details>

#### freezes module-local worker snapshots independently of live registry rows

- freezes module-local worker snapshots independently of live registry rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("freezes module-local worker snapshots independently of live registry rows")
val ctx = CompileContext.create(driver_core_compile_options_default())
ctx.mir_modules["particles"] = MirModule(name: "particles", functions: {},
    statics: {}, constants: {}, types: {})
val row = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
assert_equal(ctx.register_storage_view_evidence_batch("particles", [row]), "ok")
val before = ctx.frozen_storage_module_snapshot("particles")
assert_false(before.ok)
assert_equal(before.reason, "storage-registry-not-frozen")
_ = ctx.freeze_storage_registry()
val frozen = ctx.frozen_storage_module_snapshot("particles")
assert_true(frozen.ok)
if frozen.ok:
    assert_equal(frozen.module_name, "particles")
    assert_equal(frozen.sites.len(), 1)
    assert_equal(frozen.evidence.len(), 1)
    assert_true(frozen.module_identity.starts_with("storage-module-v1|9:particles|"))
assert_equal(ctx.frozen_storage_names_with_sites(
    ["plain", "particles"]), ["particles"])
assert_equal(ctx.frozen_storage_names_without_sites(
    ["plain", "particles"]), ["plain"])
# Sabotage the mutable registration rows after freeze. Worker input is
# the copied frozen authority and must remain unchanged.
ctx.storage_binding_module_names = []
ctx.storage_view_site_bindings = []
ctx.storage_evidence_module_names = []
ctx.storage_view_evidence_rows = []
val after = ctx.frozen_storage_module_snapshot("particles")
assert_true(after.ok)
if after.ok and frozen.ok:
    assert_equal(after.module_identity, frozen.module_identity)
    assert_equal(after.sites.len(), 1)
    assert_equal(after.evidence.len(), 1)
```

</details>

#### keeps frozen module identities scoped and stable across registration order

- keeps frozen module identities scoped and stable across registration order


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps frozen module identities scoped and stable across registration order")
val first = CompileContext.create(driver_core_compile_options_default())
val second = CompileContext.create(driver_core_compile_options_default())
val module_a = MirModule(name: "a", functions: {}, statics: {}, constants: {}, types: {})
val module_b = MirModule(name: "b", functions: {}, statics: {}, constants: {}, types: {})
first.mir_modules["a"] = module_a
first.mir_modules["b"] = module_b
second.mir_modules["a"] = module_a
second.mir_modules["b"] = module_b
val row_a = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
val row_b = MirTypedStorageViewEvidenceV1(..registry_evidence(
    StorageLayoutKind.AoS, 9, 0, "allocation:b", "snapshot:b"),
    site: mir_storage_view_site_binding_v1(42, 1, true,
        registry_site(StorageLayoutKind.AoS, 9, 0).binding))
_ = first.register_storage_view_evidence_batch("a", [row_a])
_ = first.register_storage_view_evidence_batch("b", [row_b])
_ = second.register_storage_view_evidence_batch("b", [row_b])
_ = second.register_storage_view_evidence_batch("a", [row_a])
assert_equal(first.freeze_storage_registry(), second.freeze_storage_registry())
val first_a = first.frozen_storage_module_snapshot("a")
val second_a = second.frozen_storage_module_snapshot("a")
val first_b = first.frozen_storage_module_snapshot("b")
assert_true(first_a.ok and second_a.ok and first_b.ok)
if first_a.ok and second_a.ok and first_b.ok
    and first_a.sites.len() == 1 and first_b.sites.len() == 1:
    assert_equal(first_a.module_identity, second_a.module_identity)
    assert_false(first_a.module_identity == first_b.module_identity)
    assert_true(first_a.sites[0].binding.plan.layout == StorageLayoutKind.SoA)
    assert_true(first_b.sites[0].binding.plan.layout == StorageLayoutKind.AoS)
val missing = first.frozen_storage_module_snapshot("missing")
assert_false(missing.ok)
assert_equal(missing.reason, "module-not-in-frozen-storage-registry")
first.evict_mir_module("a")
val after_evict = first.frozen_storage_module_snapshot("a")
assert_true(after_evict.ok)
if after_evict.ok and first_a.ok:
    assert_equal(after_evict.module_identity, first_a.module_identity)
```

</details>

#### freezes zero-site module membership without live MIR lookup

- freezes zero-site module membership without live MIR lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("freezes zero-site module membership without live MIR lookup")
val ctx = CompileContext.create(driver_core_compile_options_default())
ctx.mir_modules["plain"] = MirModule(name: "plain", functions: {},
    statics: {}, constants: {}, types: {})
_ = ctx.freeze_storage_registry()
ctx.evict_mir_module("plain")
val plain = ctx.frozen_storage_module_snapshot("plain")
assert_true(plain.ok)
if plain.ok:
    assert_equal(plain.sites.len(), 0)
    assert_equal(plain.evidence.len(), 0)
```

</details>

#### establishes the bootstrap-direct zero-site snapshot boundary

- establishes the bootstrap-direct zero-site snapshot boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("establishes the bootstrap-direct zero-site snapshot boundary")
val ctx = CompileContext.create(driver_core_compile_options_default())
ctx.bootstrap_entry_mir_name = "entry"
ctx.bootstrap_entry_mir = Some(MirModule(name: "entry", functions: {},
    statics: {}, constants: {}, types: {}))
ctx.mir_modules["entry"] = ctx.bootstrap_entry_mir.unwrap()
val frozen = ctx.freeze_storage_registry()
assert_true(frozen.starts_with("frozen:"))
val entry = ctx.frozen_storage_module_snapshot("entry")
assert_true(entry.ok)
if entry.ok:
    assert_equal(entry.sites.len(), 0)
    assert_equal(entry.evidence.len(), 0)

val malformed = CompileContext.create(driver_core_compile_options_default())
malformed.bootstrap_entry_mir_name = "entry"
malformed.storage_binding_module_names = ["entry"]
assert_equal(malformed.freeze_storage_registry(), "invalid")
```

</details>

#### rejects mismatched evidence and delimiter-shaped identity collisions

- rejects mismatched evidence and delimiter-shaped identity collisions


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects mismatched evidence and delimiter-shaped identity collisions")
val mismatch = CompileContext.create(driver_core_compile_options_default())
mismatch.mir_modules["particles"] = MirModule(name: "particles", functions: {},
    statics: {}, constants: {}, types: {})
val valid = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation|a", "snapshot;a")
assert_equal(mismatch.register_storage_view_evidence_batch("particles", [valid]), "ok")
var mismatched_rows = mismatch.storage_view_evidence_rows
mismatched_rows[0] = MirTypedStorageViewEvidenceV1(
    ..valid, site: registry_site(StorageLayoutKind.AoS, 7, 0))
mismatch.storage_view_evidence_rows = mismatched_rows
assert_equal(mismatch.freeze_storage_registry(), "invalid")

val first = CompileContext.create(driver_core_compile_options_default())
val second = CompileContext.create(driver_core_compile_options_default())
first.mir_modules["a|b"] = MirModule(name: "a|b", functions: {}, statics: {}, constants: {}, types: {})
second.mir_modules["a"] = MirModule(name: "a", functions: {}, statics: {}, constants: {}, types: {})
_ = first.register_storage_view_evidence_batch("a|b", [
    registry_evidence(StorageLayoutKind.SoA, 7, 64, "c", "snapshot")])
_ = second.register_storage_view_evidence_batch("a", [
    registry_evidence(StorageLayoutKind.SoA, 7, 64, "b|c", "snapshot")])
assert_false(first.freeze_storage_registry() == second.freeze_storage_registry())
```

</details>

#### captures MIR and storage authority before live context replacement

- captures MIR and storage authority before live context replacement


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("captures MIR and storage authority before live context replacement")
val ctx = CompileContext.create(driver_core_compile_options_default())
val original_a = MirModule(name: "a", functions: {}, statics: {}, constants: {}, types: {})
val original_b = MirModule(name: "b", functions: {}, statics: {}, constants: {}, types: {})
ctx.mir_modules["a"] = original_a
ctx.mir_modules["b"] = original_b
val row = registry_evidence(StorageLayoutKind.SoA, 7, 64,
    "allocation:a", "snapshot:a")
assert_equal(ctx.register_storage_view_evidence_batch("a", [row]), "ok")
_ = ctx.freeze_storage_registry()
val batch = ctx.freeze_native_module_capsules_v1(["b", "a"],
    "/tmp/capsule", "native", "x86_64", "baseline", 2, false)
assert_true(batch.ok)
if batch.ok:
    val a = batch.find("a")
    val b = batch.find("b")
    assert_true(a.ok and b.ok)
    if a.ok and b.ok:
        assert_equal(a.storage_snapshot.sites.len(), 1)
        assert_equal(b.storage_snapshot.sites.len(), 0)
        assert_equal(a.mir_module.name, "a")
        assert_equal(b.mir_module.name, "b")
        assert_false(a.capsule_identity == b.capsule_identity)
    ctx.mir_modules["a"] = MirModule(name: "replacement", functions: {},
        statics: {}, constants: {}, types: {})
    ctx.evict_mir_module("b")
    ctx.storage_binding_module_names = []
    ctx.storage_view_site_bindings = []
    assert_equal(batch.find("a").mir_module.name, "a")
    assert_equal(batch.find("b").mir_module.name, "b")
    assert_equal(batch.find("a").storage_snapshot.sites.len(), 1)
```

</details>

#### routes four frozen capsules through the parallel builder branch

- routes four frozen capsules through the parallel builder branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("routes four frozen capsules through the parallel builder branch")
val ctx = CompileContext.create(driver_core_compile_options_default())
for name in ["a", "b", "c", "d"]:
    ctx.mir_modules[name] = MirModule(name: name, functions: {},
        statics: {}, constants: {}, types: {})
_ = ctx.register_storage_view_evidence_batch("a", [
    registry_evidence(StorageLayoutKind.SoA, 7, 64,
        "allocation:a", "snapshot:a")])
val row_b = MirTypedStorageViewEvidenceV1(..registry_evidence(
    StorageLayoutKind.AoS, 9, 0, "allocation:b", "snapshot:b"),
    site: mir_storage_view_site_binding_v1(42, 1, true,
        registry_site(StorageLayoutKind.AoS, 9, 0).binding))
_ = ctx.register_storage_view_evidence_batch("b", [row_b])
_ = ctx.freeze_storage_registry()
val batch = ctx.freeze_native_module_capsules_v1(["d", "b", "a", "c"],
    "/tmp/capsule", "native", "x86_64", "baseline", 2, false)
assert_true(batch.ok)
if batch.ok:
    var builder = ParallelBuilder.create(ParallelBuildConfig(
        num_threads: 2, parallel_threshold: 4,
        deterministic: false, verbose: false))
    for name in ["d", "b", "a", "c"]:
        builder.add_unit(name, [])
    val result = builder.build(route_frozen_capsule(batch, _1))
    assert_true(result.success)
    assert_equal(result.stats.total_units, 4)
    assert_equal(result.stats.completed, 4)
    assert_equal(result.stats.failed, 0)
    assert_true(result.stats.parallel_batches > 0)
    assert_equal(result.outputs.len(), 4)
```

</details>

#### fails closed on duplicate capsule lookup and reachable identity mutation

- fails closed on duplicate capsule lookup and reachable identity mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails closed on duplicate capsule lookup and reachable identity mutation")
val ctx = CompileContext.create(driver_core_compile_options_default())
ctx.mir_modules["a"] = MirModule(name: "a", functions: {}, statics: {}, constants: {}, types: {})
_ = ctx.register_storage_view_evidence_batch("a", [
    registry_evidence(StorageLayoutKind.SoA, 7, 64,
        "allocation:a", "snapshot:a")])
_ = ctx.freeze_storage_registry()
val batch = ctx.freeze_native_module_capsules_v1(["a"],
    "/tmp/capsule", "native", "x86_64", "baseline", 2, false)
assert_true(batch.ok)
if batch.ok:
    val capsule = batch.find("a")
    assert_true(capsule.ok and capsule.identity_valid())
    val duplicate_batch = FrozenNativeModuleCapsuleBatchV1(ok: true,
        registry_identity: batch.registry_identity,
        capsules: [capsule, capsule], reason: "ok")
    assert_false(duplicate_batch.find("a").ok)
    assert_equal(duplicate_batch.find("a").reason, "duplicate-capsule")
    var changed_sites = capsule.storage_snapshot.sites
    changed_sites[0] = registry_site(StorageLayoutKind.AoS, 7, 0)
    capsule.storage_snapshot.sites = changed_sites
    assert_false(capsule.identity_valid())
val mir_batch = ctx.freeze_native_module_capsules_v1(["a"],
    "/tmp/capsule", "native", "x86_64", "baseline", 2, false)
if mir_batch.ok:
    val mir_capsule = mir_batch.find("a")
    var changed_constants = mir_capsule.mir_module.constants
    changed_constants[SymbolId.new(999)] = MirConstant(
        symbol: SymbolId.new(999), name: "changed",
        type_: MirType.i64(), value: MirConstValue.Int(1))
    mir_capsule.mir_module = MirModule(..mir_capsule.mir_module,
        constants: changed_constants)
    assert_false(mir_capsule.identity_valid())
```

</details>

#### turns owner collection rejection into a failed build unit

- turns owner collection rejection into a failed build unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("turns owner collection rejection into a failed build unit")
var deterministic = ParallelBuilder.create(ParallelBuildConfig(
    num_threads: 1, parallel_threshold: 4,
    deterministic: true, verbose: false))
deterministic.add_unit("a", [])
deterministic.set_owner_collect(collect_fail)
val first = deterministic.build(Ok("object:" + _1))
assert_false(first.success)
assert_equal(first.stats.completed, 0)
assert_equal(first.stats.failed, 1)
assert_equal(first.outputs.len(), 0)
assert_equal(first.errors.len(), 1)

var batched = ParallelBuilder.create(ParallelBuildConfig(
    num_threads: 2, parallel_threshold: 1,
    deterministic: false, verbose: false))
batched.add_unit("a", [])
batched.set_owner_collect(collect_ok)
val second = batched.build(Ok("object:" + _1))
assert_true(second.success)
assert_equal(second.stats.completed, 1)
assert_equal(second.stats.failed, 0)
assert_equal(second.outputs.len(), 1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/storage_projection_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver-owned storage projection registry.
- driver-owned storage projection registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf6b09f44d2add8f12b0ebebd0a2daa23c511423971d495ca26fcea09a73f1a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf6b09f44d2add8f12b0ebebd0a2daa23c511423971d495ca26fcea09a73f1a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf6b09f44d2add8f12b0ebebd0a2daa23c511423971d495ca26fcea09a73f1a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/storage_projection_registry_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/storage_projection_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/storage_projection_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/storage_projection_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/storage_projection_registry_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps repeated MIR local identities isolated by module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/storage_projection_registry_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate sites without partially mutating aligned rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/storage_projection_registry_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds registration-order-independent cache identity and evicts by module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
