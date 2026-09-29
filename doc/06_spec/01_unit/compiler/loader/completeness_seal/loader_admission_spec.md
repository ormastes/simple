# Loader admission and the atomic extension registry

> Sealing freezes a universe; admission decides whether a module that shows up AFTERWARDS may join it, and the registry publishes the admitted set without ever being observable half-installed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loader admission and the atomic extension registry

Sealing freezes a universe; admission decides whether a module that shows up AFTERWARDS may join it, and the registry publishes the admitted set without ever being observable half-installed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / Loader / Completeness seal |
| Status | Active |
| Source | `test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Sealing freezes a universe; admission decides whether a module that shows up
AFTERWARDS may join it, and the registry publishes the admitted set without
ever being observable half-installed.

Covered:
- a clean post-seal candidate is admitted and publishes at generation 1
- a candidate built against a different seal hash is rejected, and that
  rejection short-circuits every later check
- a constructor missing a required operation is rejected with `E-COMPLETE-021`
- a second provider claiming a sealed constructor is rejected with
  `E-COMPLETE-020`
- an open `dyn` provider is admitted under a normal profile and rejected under
  a critical one with `E-MC-DYN-001`
- publish is all-or-nothing: a duplicate operation key, a seal drift, and an
  empty publish each leave the live registry untouched

## Scenarios

### loader admission — happy path

#### admits a clean candidate against the frozen seal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a clean candidate against the frozen seal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a clean candidate against the frozen seal")
val s = frozen_universe("hir_async.sdn")
assert_true(s.seal_hash != "<seal-failed>")
match admit_module(s, candidate("hir_gpu_candidate.sdn", s.seal_hash),
        AdmissionProfile(critical: true)):
    case Ok(am):
        assert_equal(am.module_id, "hir_gpu")
        assert_equal(am.identities.len(), 1)
        # All eight §13.2 operations arrive flattened into the table.
        assert_equal(am.op_keys.len(), 8)
        assert_equal(am.seal_hash, s.seal_hash)
    case Err(reasons):
        assert_equal(reasons.len(), 0)
```

</details>

#### publishes the admitted module as generation 1

- publishes the admitted module as generation 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("publishes the admitted module as generation 1")
val s = frozen_universe("hir_async.sdn")
match admit_module(s, candidate("hir_gpu_candidate.sdn", s.seal_hash),
        AdmissionProfile(critical: true)):
    case Err(_):
        assert_true(false)
    case Ok(am):
        match publish(empty_registry(s.seal_hash), [am]):
            case Ok(reg):
                assert_equal(reg.generation, 1)
                assert_equal(reg.entries.len(), 8)
                assert_true(reg.has_module("hir_gpu"))
            case Err(_):
                assert_true(false)
```

</details>

### loader admission — seal hash mismatch

#### rejects a candidate built against a different universe

- rejects a candidate built against a different universe


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a candidate built against a different universe")
val s = frozen_universe("hir_async.sdn")
val cand = candidate("hir_gpu_candidate.sdn", "COMPLETESEALV1-deadbeef")
match admit_module(s, cand, AdmissionProfile(critical: true)):
    case Ok(_):
        assert_true(false)
    case Err(reasons):
        # Short-circuits: once the two disagree about which universe
        # they are in, no later comparison is meaningful.
        assert_equal(reasons.len(), 1)
        assert_equal(admission_reason_code(reasons[0]), "E-COMPLETE-025")
        assert_true(admission_reason_text(reasons[0]).contains("different completeness seal"))
```

</details>

### loader admission — E-COMPLETE-021 missing required operation

#### rejects a constructor that never provides `serialize`

- rejects a constructor that never provides `serialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a constructor that never provides `serialize`")
val codes = codes_of("hir_async_missing_serialize.sdn", "hir_gpu_candidate.sdn", true)
assert_true(contains(codes, "E-COMPLETE-021"))
```

</details>

### loader admission — E-COMPLETE-020 id collision

#### rejects a second provider claiming a sealed constructor

- rejects a second provider claiming a sealed constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a second provider claiming a sealed constructor")
val codes = codes_of("hir_async_shadow_collision.sdn", "hir_async.sdn", true)
assert_true(contains(codes, "E-COMPLETE-020"))
```

</details>

#### names the holder of the identity in the diagnostic

- names the holder of the identity in the diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names the holder of the identity in the diagnostic")
val s = frozen_universe("hir_async.sdn")
match admit_module(s, candidate("hir_async_shadow_collision.sdn", s.seal_hash),
        AdmissionProfile(critical: true)):
    case Ok(_):
        assert_true(false)
    case Err(reasons):
        var seen = false
        for r in reasons:
            if admission_reason_code(r) == "E-COMPLETE-020":
                assert_true(admission_reason_text(r).contains("hir_async"))
                seen = true
        assert_true(seen)
```

</details>

### loader admission — E-MC-DYN-001 open dyn under a critical profile

#### rejects an open dyn provider when the profile is critical

- rejects an open dyn provider when the profile is critical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an open dyn provider when the profile is critical")
val codes = codes_of("ide_live_probe_dyn.sdn", "hir_gpu_candidate.sdn", true)
assert_true(contains(codes, "E-MC-DYN-001"))
```

</details>

#### admits the same provider when the profile is not critical

- admits the same provider when the profile is not critical


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits the same provider when the profile is not critical")
val codes = codes_of("ide_live_probe_dyn.sdn", "hir_gpu_candidate.sdn", false)
assert_false(contains(codes, "E-MC-DYN-001"))
```

</details>

### registry — atomic publish

#### refuses an empty publish rather than bumping a generation for nothing

- refuses an empty publish rather than bumping a generation for nothing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses an empty publish rather than bumping a generation for nothing")
val reg = empty_registry("COMPLETESEALV1-abc")
var empty_list: [AdmittedModule] = []
match publish(reg, empty_list):
    case Ok(_):
        assert_true(false)
    case Err(errs):
        assert_equal(registry_error_code(errs[0]), "E-REGISTRY-004")
```

</details>

#### refuses a module admitted under a different seal and leaves the live table intact

- refuses a module admitted under a different seal and leaves the live table intact


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a module admitted under a different seal and leaves the live table intact")
val live = empty_registry("COMPLETESEALV1-abc")
val drifted = AdmittedModule(
    module_id: "hir_drift",
    seal_hash: "COMPLETESEALV1-xyz",
    identities: [],
    op_keys: ["k#verify"],
    op_handlers: ["drift.verify"]
)
match publish(live, [drifted]):
    case Ok(_):
        assert_true(false)
    case Err(errs):
        assert_equal(registry_error_code(errs[0]), "E-REGISTRY-001")
assert_equal(live.generation, 0)
assert_equal(live.entries.len(), 0)
```

</details>

#### refuses a publish whose operation key is already installed

- refuses a publish whose operation key is already installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a publish whose operation key is already installed")
val live = empty_registry("COMPLETESEALV1-abc")
val first = AdmittedModule(
    module_id: "mod_a",
    seal_hash: "COMPLETESEALV1-abc",
    identities: [],
    op_keys: ["k#verify"],
    op_handlers: ["a.verify"]
)
val second = AdmittedModule(
    module_id: "mod_b",
    seal_hash: "COMPLETESEALV1-abc",
    identities: [],
    op_keys: ["k#verify"],
    op_handlers: ["b.verify"]
)
match publish(live, [first]):
    case Err(_):
        assert_true(false)
    case Ok(gen1):
        assert_equal(gen1.generation, 1)
        match publish(gen1, [second]):
            case Ok(_):
                assert_true(false)
            case Err(errs):
                assert_equal(registry_error_code(errs[0]), "E-REGISTRY-002")
        # The rejected publish is not visible anywhere: generation 1
        # still answers with mod_a's handler.
        match gen1.handler_for("k#verify"):
            case Some(h):
                assert_equal(h, "a.verify")
            case None:
                assert_true(false)
        assert_false(gen1.has_module("mod_b"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `85bf53f03b96726a7194a6226af20c5b66962a23ad7e7c263eff39b58ffb9c2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85bf53f03b96726a7194a6226af20c5b66962a23ad7e7c263eff39b58ffb9c2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85bf53f03b96726a7194a6226af20c5b66962a23ad7e7c263eff39b58ffb9c2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl
mirror: doc/06_spec/01_unit/compiler/loader/completeness_seal/loader_admission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/loader/completeness_seal/loader_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/loader/completeness_seal/loader_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a clean candidate against the frozen seal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the admitted module as generation 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/loader/completeness_seal/loader_admission_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a candidate built against a different universe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
