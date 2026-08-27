# SIF Round-Trip and Canonical Determinism

> (startup_perf_architecture_2026-08-17.md §10.2): incremental rebuild had no

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SIF Round-Trip and Canonical Determinism

(startup_perf_architecture_2026-08-17.md §10.2): incremental rebuild had no

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/driver/sif_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Reproduces:** audit gap #19 — no Simple Interface Format existed
(startup_perf_architecture_2026-08-17.md §10.2): incremental rebuild had no
separable module-interface artifact to query.

A SIF is a versioned, canonical, deterministic serialization of a module's
exported interface (src/compiler/80.driver/sif/sif.spl). This spec proves:
- a serialized SIF validates and round-trips through its accessors;
- serialization is order-insensitive: any input ordering of parts and deps
  produces BYTE-IDENTICAL text and an identical digest;
- the embedded iface-digest is EXACTLY action_key.interface_digest_of over
  the part set, so it composes with ActionDep.iface_digest /
  dependency_interface_fold without re-derivation.

## Scenarios

### SIF round-trip

#### serializes to a valid SIF and round-trips every field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serializes to a valid SIF and round-trips every field


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes to a valid SIF and round-trips every field")
val s = sif_serialize_parts("demo.mod", "lang1", DEPS_A, PARTS_A)
assert_equal(sif_validate(s), "")
assert_equal(sif_module_id(s), "demo.mod")
assert_equal(sif_lang_version(s), "lang1")
val deps = sif_dep_entries(s)
assert_equal(deps.len(), 2)
assert_equal(deps[0], "mod.a=digesta")
assert_equal(deps[1], "mod.b=digestb")
val parts = sif_parts(s)
assert_equal(parts.len(), 3)
assert_true(sif_iface_digest(s) != "")
```

</details>

#### is byte-identical across part and dep reorderings

- is byte-identical across part and dep reorderings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is byte-identical across part and dep reorderings")
val a = sif_serialize_parts("demo.mod", "lang1", DEPS_A, PARTS_A)
val b = sif_serialize_parts("demo.mod", "lang1", DEPS_A_REORDERED, PARTS_A_REORDERED)
assert_equal(a, b)
assert_equal(sif_iface_digest(a), sif_iface_digest(b))
```

</details>

#### embeds exactly interface_digest_of(parts) — composes with action_key

- embeds exactly interface_digest_of(parts) — composes with action_key


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("embeds exactly interface_digest_of(parts) — composes with action_key")
val s = sif_serialize_parts("demo.mod", "lang1", DEPS_A, PARTS_A)
assert_equal(sif_iface_digest(s), interface_digest_of(PARTS_A))
# And that digest drops straight into the dependency fold.
val fold = dependency_interface_fold(["demo.mod=" + sif_iface_digest(s)])
assert_true(fold != "")
```

</details>

#### builds from raw source with declaration-order independence

- builds from raw source with declaration-order independence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds from raw source with declaration-order independence")
val src1 = "fn f() -> i64:\n    1\nfn g() -> i64:\n    2\n"
val src2 = "fn g() -> i64:\n    2\nfn f() -> i64:\n    1\n"
val a = sif_of_source("demo.src", "lang1", [], src1)
val b = sif_of_source("demo.src", "lang1", [], src2)
assert_equal(sif_validate(a), "")
assert_equal(a, b)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2b113e4e77ce6040e56d912665175d2cc520ca06aaf0a3109745e8cb671a1288`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2b113e4e77ce6040e56d912665175d2cc520ca06aaf0a3109745e8cb671a1288`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2b113e4e77ce6040e56d912665175d2cc520ca06aaf0a3109745e8cb671a1288`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/sif_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/sif_roundtrip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/sif_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/sif_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/sif_roundtrip_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes to a valid SIF and round-trips every field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/sif_roundtrip_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is byte-identical across part and dep reorderings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/sif_roundtrip_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'embeds exactly interface_digest_of(parts) — composes with action_key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
