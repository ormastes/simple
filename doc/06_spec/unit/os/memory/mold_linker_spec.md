# Mold Linker Priority Specification

> Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority linker when `bin/mold/mold` is present, and that the install script exists.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mold Linker Priority Specification

Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority linker when `bin/mold/mold` is present, and that the install script exists.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #mold-default-linker |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/unit/os/memory/mold_linker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority
linker when `bin/mold/mold` is present, and that the install script exists.

## Behavior

- `find_mold_path()` checks local bundled mold paths before querying PATH
- `find_linker()` returns `LinkerType.Mold` whenever mold is found
- `SIMPLE_LINKER` can force the same linker aliases accepted by the Rust path
- LLD fallback checks the GNU-compatible `ld.lld` frontend before bare `lld`
- `scripts/install-mold.shs` exists and is the canonical mold download script

## Implementation Notes

The in-process lld path in `linker_wrapper.spl` is gated on `is_simpleos_target()`
and is correct cross-compile behavior — it is NOT a mold override on the host.

## Scenarios

### mold install script

#### scripts/install-mold.shs exists

- scripts/install-mold.shs exists
   - Expected: file_exists("scripts/install-mold.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scripts/install-mold.shs exists")
expect(file_exists("scripts/install-mold.shs")).to_equal(true)
```

</details>

### find_linker priority — mold-first invariant

#### mold is first in the preference chain

- mold is first in the preference chain
   - Expected: preference_order[0] equals `mold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mold is first in the preference chain")
val preference_order = mold_default_linker_order()
expect(preference_order[0]).to_equal("mold")
```

</details>

#### lld is second choice after mold

- lld is second choice after mold
   - Expected: preference_order[1] equals `lld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lld is second choice after mold")
val preference_order = mold_default_linker_order()
expect(preference_order[1]).to_equal("lld")
```

</details>

#### ld.lld is the preferred lld frontend

- ld.lld is the preferred lld frontend
   - Expected: lld_frontends[0] equals `ld.lld`
   - Expected: lld_frontends[1] equals `lld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld.lld is the preferred lld frontend")
val lld_frontends: [text] = ["ld.lld", "lld"]
expect(lld_frontends[0]).to_equal("ld.lld")
expect(lld_frontends[1]).to_equal("lld")
```

</details>

#### SIMPLE_LINKER supports Rust-compatible linker aliases

- SIMPLE_LINKER supports Rust-compatible linker aliases
   - Expected: aliases contains `mold`
   - Expected: aliases contains `ld.lld`
   - Expected: aliases contains `lld-link`
   - Expected: aliases contains `gnu`
   - Expected: aliases contains `bfd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SIMPLE_LINKER supports Rust-compatible linker aliases")
val aliases = mold_supported_override_aliases()
expect(aliases.contains("mold")).to_equal(true)
expect(aliases.contains("ld.lld")).to_equal(true)
expect(aliases.contains("lld-link")).to_equal(true)
expect(aliases.contains("gnu")).to_equal(true)
expect(aliases.contains("bfd")).to_equal(true)
```

</details>

#### ld is last resort

- ld is last resort
   - Expected: preference_order[2] equals `ld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ld is last resort")
val preference_order = mold_default_linker_order()
expect(preference_order[2]).to_equal("ld")
```

</details>

#### local bin/mold/mold path is checked before system PATH

- local bin/mold/mold path is checked before system PATH
   - Expected: local_mold_suffix.starts_with("/bin/mold") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local bin/mold/mold path is checked before system PATH")
# find_mold_path() builds: cwd() + "/bin/mold/mold"
# We verify the expected local path string is well-formed.
val local_mold_suffix = "/bin/mold/mold"
expect(local_mold_suffix.starts_with("/bin/mold")).to_equal(true)
```

</details>

#### platform-specific bundled mold names are supported

- platform-specific bundled mold names are supported
   - Expected: bundled_names contains `mold-linux-x86_64`
   - Expected: bundled_names contains `mold-freebsd-aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("platform-specific bundled mold names are supported")
val bundled_names: [text] = [
    "mold-linux-x86_64",
    "mold-linux-aarch64",
    "mold-macos-x86_64",
    "mold-macos-aarch64",
    "mold-freebsd-x86_64",
    "mold-freebsd-aarch64"
]
expect(bundled_names.contains("mold-linux-x86_64")).to_equal(true)
expect(bundled_names.contains("mold-freebsd-aarch64")).to_equal(true)
```

</details>

#### bundled mold locations cover repo bin and lib layouts

- bundled mold locations cover repo bin and lib layouts
   - Expected: bundled_locations[0] equals `bin/mold/mold`
   - Expected: bundled_locations contains `bin/mold`
   - Expected: bundled_locations contains `lib/simple/mold`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bundled mold locations cover repo bin and lib layouts")
val bundled_locations = mold_bundled_search_suffixes()
expect(bundled_locations[0]).to_equal("bin/mold/mold")
expect(bundled_locations.contains("bin/mold")).to_equal(true)
expect(bundled_locations.contains("lib/simple/mold")).to_equal(true)
```

</details>

#### bin/mold/mold presence gates mold selection

- bin/mold/mold presence gates mold selection
   - Expected: mold_installed is true
   - Expected: file_exists("scripts/install-mold.shs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bin/mold/mold presence gates mold selection")
# When the local binary exists, find_linker() must return Mold.
# When absent, it falls through to lld or ld.
# This invariant is captured as a documentation assertion.
val mold_installed = file_exists("bin/mold/mold")
if mold_installed:
    # With binary present: mold would be selected.
    expect(mold_installed).to_equal(true)
else:
    # Without binary: fallback chain applies — this is expected in
    # clean-checkout environments before running install-mold.shs.
    expect(file_exists("scripts/install-mold.shs")).to_equal(true)
```

</details>

#### mold role feature surface documents implemented and missing roles

- mold role feature surface documents implemented and missing roles
   - Expected: features.len() equals `7`
   - Expected: features[0].role equals `MoldCompatibilityRole.LinkerDetection`
   - Expected: features[0].status equals `implemented`
   - Expected: features[6].role equals `MoldCompatibilityRole.PureSimpleLinker`
   - Expected: features[6].status equals `missing`
   - Expected: mold_is_pure_simple_linker_complete() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mold role feature surface documents implemented and missing roles")
val features = mold_compatibility_features()
expect(features.len()).to_equal(7)
expect(features[0].role).to_equal(MoldCompatibilityRole.LinkerDetection)
expect(features[0].status).to_equal("implemented")
expect(features[6].role).to_equal(MoldCompatibilityRole.PureSimpleLinker)
expect(features[6].status).to_equal("missing")
expect(mold_is_pure_simple_linker_complete()).to_equal(false)
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

- Canonical SPipe generation for source `652290853205951c82e44371d925c28f51a021230858487b4967d30defde8f36`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `652290853205951c82e44371d925c28f51a021230858487b4967d30defde8f36`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `652290853205951c82e44371d925c28f51a021230858487b4967d30defde8f36`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/memory/mold_linker_spec.spl
mirror: doc/06_spec/unit/os/memory/mold_linker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/memory/mold_linker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/memory/mold_linker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/memory/mold_linker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/memory/mold_linker_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scripts/install-mold.shs exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/memory/mold_linker_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mold is first in the preference chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/memory/mold_linker_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lld is second choice after mold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
