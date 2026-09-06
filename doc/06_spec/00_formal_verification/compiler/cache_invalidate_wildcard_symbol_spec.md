# VerificationCache.invalidate_dependents — the "*" wildcard must not alias units

> `ProofUnit.source_symbol` is documented at `src/compiler_rust/lib/std/src/verification/proof_unit.spl:14` as "Primary symbol (fn/class name, or `*` for file-level)".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VerificationCache.invalidate_dependents — the "*" wildcard must not alias units

`ProofUnit.source_symbol` is documented at `src/compiler_rust/lib/std/src/verification/proof_unit.spl:14` as "Primary symbol (fn/class name, or `*` for file-level)".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure / verification cache correctness |
| Status | Regression guard |
| Source | `test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`ProofUnit.source_symbol` is documented at
`src/compiler_rust/lib/std/src/verification/proof_unit.spl:14` as
"Primary symbol (fn/class name, or `*` for file-level)".

`invalidate_dependents` grew its transitive walk by seeding the invalidated
unit's `source_file`, `lean_module` AND `source_symbol` into `changed_keys`,
then matching later units against that same set. For a **file-level** unit the
symbol is the literal `"*"`, which is not a symbol name at all — it is a
wildcard shared by every file-level unit in the program. Seeding it made all
file-level units alias to one another, so invalidating a single genuine
dependent cascaded into a full cache wipe.

Both the repro and the generalization below exercise the same public API the
compiler driver uses; nothing is stubbed.

## Scenarios

### invalidate_dependents wildcard aliasing

#### repro — the exact shape that regressed

#### preserves a non-dependent file-level unit

- preserves a non-dependent file-level unit
   - Expected: entry.fingerprint equals `fp_a.combined`
   - Expected: "a.spl was evicted" equals `a.spl preserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FORMALVERIFI
step("preserves a non-dependent file-level unit")
var cache = VerificationCache.new("/tmp/test-vcache-wildcard-repro")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")

var unit_a = ProofUnit.create("a.spl", "*", "Verification.A", "a.lean")
var unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean")
unit_b = unit_b.with_dependencies(["base_defs"])

cache.invalidate_dependents("base_defs", [unit_a, unit_b])

# the dependent is gone ...
expect(cache.lookup("b.spl", fp_b)).to_be_nil()
# ... and the non-dependent survived
val result_a = cache.lookup("a.spl", fp_a)
match result_a:
    case Some(entry):
        expect(entry.fingerprint).to_equal(fp_a.combined)
    case nil:
        expect("a.spl was evicted").to_equal("a.spl preserved")
```

</details>

#### generalization — the property, not the one shape

#### evicts only the dependent among many file-level units

- evicts only the dependent among many file-level units


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FORMALVERIFI
step("evicts only the dependent among many file-level units")
var cache = VerificationCache.new("/tmp/test-vcache-wildcard-many")
val names = ["u0.spl", "u1.spl", "u2.spl", "u3.spl", "u4.spl"]
var units: [ProofUnit] = []
var fps: [Fingerprint] = []
var i = 0
for n in names:
    val fp = Fingerprint.from_hashes(n, "lean-{i}", [], "v4.x")
    fps = fps.push(fp)
    cache.store(n, fp, VerificationState.Verified, {}, "v4.x")
    var u = ProofUnit.create(n, "*", "Verification.U{i}", "u{i}.lean")
    # only u2 depends on the changed module
    if n == "u2.spl":
        u = u.with_dependencies(["base_defs"])
    units = units.push(u)
    i = i + 1

cache.invalidate_dependents("base_defs", units)

expect(cache.lookup("u2.spl", fps[2])).to_be_nil()
# the other four are untouched.
# NOTE: `.?` yields the PAYLOAD, not a bool, so `expect(x.?).to_equal(true)`
# compares a CacheEntry against `true` and always fails. Use to_be_truthy.
expect(cache.lookup("u0.spl", fps[0])).to_be_truthy()
expect(cache.lookup("u1.spl", fps[1])).to_be_truthy()
expect(cache.lookup("u3.spl", fps[3])).to_be_truthy()
expect(cache.lookup("u4.spl", fps[4])).to_be_truthy()
```

</details>

#### does not treat the bare wildcard as a changed-module key

- does not treat the bare wildcard as a changed-module key


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FORMALVERIFI
step("does not treat the bare wildcard as a changed-module key")
var cache = VerificationCache.new("/tmp/test-vcache-wildcard-bare")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
val unit_a = ProofUnit.create("a.spl", "*", "Verification.A", "a.lean")

# Invalidating "*" must not be read as "everything file-level".
cache.invalidate_dependents("*", [unit_a])

expect(cache.lookup("a.spl", fp_a)).to_be_truthy()
```

</details>

#### still propagates through a real named symbol

- still propagates through a real named symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FORMALVERIFI
step("still propagates through a real named symbol")
"""
The fix excludes only the literal "*". A genuine symbol name must
keep working as a transitive key, otherwise the fix would have
traded over-invalidation for under-invalidation.
"""
var cache = VerificationCache.new("/tmp/test-vcache-named-symbol")
val fp_a = Fingerprint.from_hashes("a", "la", [], "v4.x")
val fp_b = Fingerprint.from_hashes("b", "lb", [], "v4.x")
cache.store("a.spl", fp_a, VerificationState.Verified, {}, "v4.x")
cache.store("b.spl", fp_b, VerificationState.Verified, {}, "v4.x")

# a.spl is keyed by the named symbol "helper_fn"
val unit_a = ProofUnit.create("a.spl", "helper_fn", "Verification.A", "a.lean")
# b.spl depends on that symbol
var unit_b = ProofUnit.create("b.spl", "*", "Verification.B", "b.lean")
unit_b = unit_b.with_dependencies(["helper_fn"])

cache.invalidate_dependents("helper_fn", [unit_a, unit_b])

expect(cache.lookup("a.spl", fp_a)).to_be_nil()
expect(cache.lookup("b.spl", fp_b)).to_be_nil()
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

- `REQ-SSPEC-FORMALVERIFI`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0b6dd3f699a76985363633d71347a376d9949b8b3d70967053f76ec0b0f6fe4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0b6dd3f699a76985363633d71347a376d9949b8b3d70967053f76ec0b0f6fe4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0b6dd3f699a76985363633d71347a376d9949b8b3d70967053f76ec0b0f6fe4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl
mirror: doc/06_spec/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a non-dependent file-level unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evicts only the dependent among many file-level units' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/00_formal_verification/compiler/cache_invalidate_wildcard_symbol_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not treat the bare wildcard as a changed-module key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
