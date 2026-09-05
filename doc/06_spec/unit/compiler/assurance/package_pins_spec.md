# Package Pins Specification

> Tests covering package pin profile key, waiver hygiene, dependency closure, critical check enforcement, whole-report gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Pins Specification

## Scenarios

### package pin profile key

#### defaults an unpinned manifest to robust and marks it not explicit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-HARDENING-PHASE8-PINS
```

</details>

#### records an explicit profile pin

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = pin_of("project:\n  name: pinned\n  profile: critical\n", "fx/pinned")
assert_equal(p.profile, "critical")
assert_true(p.explicit)
```

</details>

#### accepts `critical: true` as sugar for profile: critical

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = pin_of("project:\n  name: sugar\n  critical: true\n", "fx/sugar")
assert_equal(p.profile, "critical")
assert_true(p.explicit)
```

</details>

#### rejects an unknown profile spelling instead of silently downgrading

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_package_pin("project:\n  name: bad\n  profile: paranoid\n", "p", "d"):
    case Ok(_): assert_true(false)
    case Err(errs): expect(errs.len()).to_be_greater_than(0)
```

</details>

#### ranks profiles strictness-ascending and gives an unknown name -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(profile_rank("moderate")).to_be_less_than(profile_rank("robust"))
expect(profile_rank("robust")).to_be_less_than(profile_rank("critical"))
assert_equal(profile_rank("nonsense"), -1)
assert_false(is_at_least_robust("nonsense"))
assert_false(is_at_least_robust("moderate"))
assert_true(is_at_least_robust("robust"))
assert_true(is_at_least_robust("critical"))
```

</details>

### waiver hygiene

#### accepts a waiver with an owner and a future expiry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = core_with("\nassurance:\n  waivers:\n    - rule: R1\n      owner: team\n      expires: 2099-01-01\n")
assert_equal(check_waivers(p, "2026-08-21").len(), 0)
```

</details>

#### flags a waiver with no owner as E-PIN-001

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = core_with("\nassurance:\n  waivers:\n    - rule: R1\n      expires: 2099-01-01\n")
val rs = check_waivers(p, "2026-08-21")
assert_equal(rs.len(), 1)
assert_equal(pin_reason_code(rs[0]), "E-PIN-001")
```

</details>

#### flags a waiver with no expiry as E-PIN-002

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = core_with("\nassurance:\n  waivers:\n    - rule: R1\n      owner: team\n")
val rs = check_waivers(p, "2026-08-21")
assert_equal(rs.len(), 1)
assert_equal(pin_reason_code(rs[0]), "E-PIN-002")
```

</details>

#### flags an expired waiver as E-PIN-003

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = core_with("\nassurance:\n  waivers:\n    - rule: R1\n      owner: team\n      expires: 2020-01-01\n")
val rs = check_waivers(p, "2026-08-21")
assert_equal(rs.len(), 1)
assert_equal(pin_reason_code(rs[0]), "E-PIN-003")
```

</details>

#### still reports a MISSING owner when no date is supplied

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# An empty `today` disables only the expiry comparison. A caller that
# forgets the date must get fewer findings, never a silent pass on a
# field that is absent outright.
val p = core_with("\nassurance:\n  waivers:\n    - rule: R1\n      expires: 2020-01-01\n")
val rs = check_waivers(p, "")
assert_equal(rs.len(), 1)
assert_equal(pin_reason_code(rs[0]), "E-PIN-001")
```

</details>

### dependency closure

#### normalizes and joins relative project paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(normalize_path("src/compiler/00.common/../../lib"), "src/lib")
assert_equal(join_path("src/compiler/00.common", "../../lib"), "src/lib")
assert_equal(join_path("src/lib", "./."), "src/lib")
```

</details>

#### resolves a path edge to the package whose manifest sits in that directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib = pin_of("project:\n  name: simple-std\n", "src/lib")
val common = pin_of("project:\n  name: common\n  profile: critical\n"
    + "  dependencies:\n    - project: ../../lib\n", "src/compiler/00.common")
assert_equal(resolve_edges([lib, common], common), ["simple-std"])
```

</details>

#### carries an unresolvable edge instead of dropping it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orphan = pin_of("project:\n  name: orphan\n  profile: critical\n"
    + "  dependencies:\n    - project: ../nowhere\n", "fx/orphan")
val edges = resolve_edges([orphan], orphan)
assert_equal(edges.len(), 1)
assert_true(is_unresolved(edges[0]))
```

</details>

#### is transitive and terminates on a cycle

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = pin_of("project:\n  name: a\n  dependencies:\n    - package: b\n", "fx/a")
val b = pin_of("project:\n  name: b\n  dependencies:\n    - package: c\n", "fx/b")
val c = pin_of("project:\n  name: c\n  dependencies:\n    - package: a\n", "fx/c")
val closure = dependency_closure([a, b, c], a)
assert_equal(closure.len(), 2)
assert_true(closure.contains("b"))
assert_true(closure.contains("c"))
```

</details>

#### rejects a critical pin whose closure holds a below-robust package as E-PIN-004

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val weak = pin_of("project:\n  name: base\n  profile: moderate\n", "fx/base")
val core = core_with("")
val rs = check_critical_preconditions([weak, core], core, CLEAN_CHECKS)
assert_equal(count_with_code(rs, "E-PIN-004"), 1)
```

</details>

#### rejects a critical pin whose closure cannot be resolved as E-PIN-004

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orphan = pin_of("project:\n  name: core\n  profile: critical\n"
    + "  dependencies:\n    - project: ../nowhere\n", "fx/core")
val rs = check_critical_preconditions([orphan], orphan, CLEAN_CHECKS)
assert_equal(count_with_code(rs, "E-PIN-004"), 1)
```

</details>

### critical check enforcement

#### accepts a critical pin when every covering check is mandatory and one is differential

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core = core_with("")
assert_equal(check_critical_preconditions([BASE, core], core, CLEAN_CHECKS).len(), 0)
```

</details>

#### rejects an advisory covering check as E-PIN-005

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val advisory = checks_of(
    "checks:\n"
    + "  - name: check-structure.shs\n    status: advisory\n    differential: false\n    covers:\n      - core\n"
    + "  - name: check-parity.shs\n    status: mandatory\n    differential: true\n    covers:\n      - core\n")
val core = core_with("")
val rs = check_critical_preconditions([BASE, core], core, advisory)
assert_equal(count_with_code(rs, "E-PIN-005"), 1)
```

</details>

#### rejects a package with no differential coverage as E-PIN-006

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nodiff = checks_of(
    "checks:\n"
    + "  - name: check-structure.shs\n    status: mandatory\n    differential: false\n    covers:\n      - core\n")
val core = core_with("")
val rs = check_critical_preconditions([BASE, core], core, nodiff)
assert_equal(count_with_code(rs, "E-PIN-006"), 1)
```

</details>

#### does not count an ADVISORY differential check as coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Precondition 4 is satisfied by a differential gate that RUNS. An
# advisory one proves nothing, so it must trigger both E-PIN-005 and
# E-PIN-006 rather than laundering itself into coverage.
val advisory_diff = checks_of(
    "checks:\n"
    + "  - name: check-parity.shs\n    status: advisory\n    differential: true\n    covers:\n      - core\n")
val core = core_with("")
val rs = check_critical_preconditions([BASE, core], core, advisory_diff)
assert_equal(count_with_code(rs, "E-PIN-005"), 1)
assert_equal(count_with_code(rs, "E-PIN-006"), 1)
```

</details>

#### rejects a check manifest with an unknown status instead of reading it as mandatory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_critical_checks("checks:\n  - name: c.shs\n    status: maybe\n", "<f>"):
    case Ok(_): assert_true(false)
    case Err(errs): expect(errs.len()).to_be_greater_than(0)
```

</details>

#### rejects an empty check manifest as non-evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match parse_critical_checks("checks: []\n", "<f>"):
    case Ok(_): assert_true(false)
    case Err(errs): expect(errs.len()).to_be_greater_than(0)
```

</details>

### whole-report gate

#### counts explicit pins only, not inherited defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plain = pin_of("project:\n  name: plain\n", "fx/plain")
val core = core_with("")
val rep = check_package_pins([plain, BASE, core], CLEAN_CHECKS, "2026-08-21")
# BASE and core declare `profile:`; plain does not.
assert_equal(rep.pinned, 2)
assert_equal(rep.critical, 1)
assert_equal(rep.reasons.len(), 0)
```

</details>

#### applies critical preconditions only to critical packages

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `base` is robust and covered by nothing; that is fine. Only `core`'s
# pin is subject to preconditions 2-4.
val core = core_with("")
val rep = check_package_pins([BASE, core], CLEAN_CHECKS, "2026-08-21")
assert_equal(rep.reasons.len(), 0)
```

</details>

#### reports blockers for a package that is deliberately still robust

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nodiff = checks_of(
    "checks:\n"
    + "  - name: check-structure.shs\n    status: mandatory\n    differential: false\n    covers:\n      - core\n")
val core = pin_of("project:\n  name: core\n  profile: robust\n"
    + "  dependencies:\n    - package: base\n", "fx/core")
val rep = check_package_pins([BASE, core], nodiff, "2026-08-21")
# Still-robust: the gate itself is clean...
assert_equal(rep.reasons.len(), 0)
# ...but `--why` names exactly what would block a critical pin.
val blockers = blockers_for_critical([BASE, core], "core", nodiff, "2026-08-21")
assert_equal(count_with_code(blockers, "E-PIN-006"), 1)
```

</details>

#### gives every closed reason a distinct code and a non-empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rs: [PinReason] = [
    PinReason.WaiverWithoutOwner("p", "r"),
    PinReason.WaiverWithoutExpiry("p", "r"),
    PinReason.WaiverExpired("p", "r", "2020-01-01"),
    PinReason.DependencyBelowRobust("p", "d", "moderate"),
    PinReason.AdvisoryCheckInCritical("p", "c.shs"),
    PinReason.NoDifferentialCoverage("p")
]
var codes: [text] = []
for r in rs:
    val code = pin_reason_code(r)
    assert_false(codes.contains(code))
    codes = codes + [code]
    expect(pin_reason_text(r)).to_start_with(code)
assert_equal(codes.len(), 6)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/assurance/package_pins_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering package pin profile key, waiver hygiene, dependency closure, critical check enforcement, whole-report gate.
- package pin profile key
- waiver hygiene
- dependency closure
- critical check enforcement
- whole-report gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-HARDENING-PHASE8-PINS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `43191dc756e765cce667e760b87c3e0485d5754b2b18fe0a0b027632451a38ed`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `43191dc756e765cce667e760b87c3e0485d5754b2b18fe0a0b027632451a38ed`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `43191dc756e765cce667e760b87c3e0485d5754b2b18fe0a0b027632451a38ed`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/compiler/assurance/package_pins_spec.spl
mirror: doc/06_spec/unit/compiler/assurance/package_pins_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/assurance/package_pins_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/assurance/package_pins_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/assurance/package_pins_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/unit/compiler/assurance/package_pins_spec.spl:65:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defaults an unpinned manifest to robust and marks it not explicit' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/assurance/package_pins_spec.spl:76:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records an explicit profile pin' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/assurance/package_pins_spec.spl:82:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'accepts `critical: true` as sugar for profile: critical' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/compiler/assurance/package_pins_spec.spl:88:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects an unknown profile spelling instead of silently downgrading' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
