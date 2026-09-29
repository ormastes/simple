# Aspect Pack Forbidden Io Temporal Specification

> Tests covering E-APACK008 temporal deny — apk_loader_seal_operational_state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aspect Pack Forbidden Io Temporal Specification

## Scenarios

### E-APACK008 temporal deny — apk_loader_seal_operational_state

#### the flag starts unset and can be observed before sealing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the flag starts unset and can be observed before sealing
   - Expected: apk_loader_is_operational_sealed(ld) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the flag starts unset and can be observed before sealing")
val ld = apk_loader_new()
expect(apk_loader_is_operational_sealed(ld)).to_equal(false)
```

</details>

#### sealing flips the observable flag

- sealing flips the observable flag
   - Expected: apk_loader_is_operational_sealed(ld) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sealing flips the observable flag")
val ld = apk_loader_new()
apk_loader_seal_operational_state(ld)
expect(apk_loader_is_operational_sealed(ld)).to_equal(true)
```

</details>

#### REJECTS a lazy facet<T>() acquisition (apk_load_facet) once sealed — violating call graph

- REJECTS a lazy facet<T>() acquisition (apk_load_facet) once sealed — violating call graph
   - Expected: got.ok is false
   - Expected: got.error_code equals `E-APACK008`
   - Expected: apk_loader_packs_opened(ld) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REJECTS a lazy facet<T>() acquisition (apk_load_facet) once sealed — violating call graph")
val pack = apk_build_pack_v1(_module())
val ld = apk_loader_new()
apk_loader_register_pack(ld, "aspect/obs.apk", pack.bytes)
apk_loader_seal_operational_state(ld)
val got = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("E-APACK008")
# fail-closed: the rejected acquisition must not have opened the pack
expect(apk_loader_packs_opened(ld)).to_equal(0)
```

</details>

#### PASSES the identical lazy acquisition BEFORE sealing — legitimate call graph

- PASSES the identical lazy acquisition BEFORE sealing — legitimate call graph
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: apk_loader_packs_opened(ld) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("PASSES the identical lazy acquisition BEFORE sealing — legitimate call graph")
val pack = apk_build_pack_v1(_module())
val ld = apk_loader_new()
apk_loader_register_pack(ld, "aspect/obs.apk", pack.bytes)
val got = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
expect(apk_loader_packs_opened(ld)).to_equal(1)
```

</details>

#### PASSES try_facet<T>() after sealing — design §19 rule 3 explicitly permits it (never performs I/O)

- PASSES try_facet<T>() after sealing — design §19 rule 3 explicitly permits it (never performs I/O)
   - Expected: warm.ok is true
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: got.error_code equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("PASSES try_facet<T>() after sealing — design §19 rule 3 explicitly permits it (never performs I/O)")
val pack = apk_build_pack_v1(_module())
val ld = apk_loader_new()
apk_loader_register_pack(ld, "aspect/obs.apk", pack.bytes)
# already-bound BEFORE sealing, matching "aspects fixed before operational state"
val warm = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(warm.ok).to_equal(true)
apk_loader_seal_operational_state(ld)
val got = apk_try_facet(ld, "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(true)
expect(got.error_code).to_equal("")
```

</details>

#### a repeat apk_load_facet after sealing still PASSES once already bound — cache hit needs no I/O

- a repeat apk_load_facet after sealing still PASSES once already bound — cache hit needs no I/O
   - Expected: warm.ok is true
   - Expected: got.ok is true
   - Expected: got.error_code equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a repeat apk_load_facet after sealing still PASSES once already bound — cache hit needs no I/O")
val pack = apk_build_pack_v1(_module())
val ld = apk_loader_new()
apk_loader_register_pack(ld, "aspect/obs.apk", pack.bytes)
val warm = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(warm.ok).to_equal(true)
apk_loader_seal_operational_state(ld)
val got = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.error_code).to_equal("")
```

</details>

#### DEFECT-CLASS NEGATIVE: without the seal, the same call graph is NOT rejected — proves the check, not \

- a repeat apk_load_facet after sealing still PASSES once already bound — cache hit needs no I/O
   - Expected: got.ok is true
   - Expected: got.error_code equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a repeat apk_load_facet after sealing still PASSES once already bound — cache hit needs no I/O")
some unrelated failure, is what rejects the sealed case above (removing the check would make the \
sealed-case REJECT test above silently pass with ok:true instead of failing loudly)":
val pack = apk_build_pack_v1(_module())
val ld = apk_loader_new()
apk_loader_register_pack(ld, "aspect/obs.apk", pack.bytes)
# no seal call at all
val got = apk_load_facet(ld, _catalog_bytes(), "debug/Debuggable")
expect(got.ok).to_equal(true)
expect(got.error_code).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering E-APACK008 temporal deny — apk_loader_seal_operational_state.
- E-APACK008 temporal deny — apk_loader_seal_operational_state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ac68ca3d456e1abd13e138809c1f140fc508f4d60fdb5a45f1809b6e589f66dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac68ca3d456e1abd13e138809c1f140fc508f4d60fdb5a45f1809b6e589f66dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac68ca3d456e1abd13e138809c1f140fc508f4d60fdb5a45f1809b6e589f66dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl
mirror: doc/06_spec/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the flag starts unset and can be observed before sealing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sealing flips the observable flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/aspect_pack_forbidden_io_temporal_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REJECTS a lazy facet<T>() acquisition (apk_load_facet) once sealed — violating call graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
