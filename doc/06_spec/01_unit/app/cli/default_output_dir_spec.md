# Default Output Dir Specification

> Tests covering native-build default output containment (task #35).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Output Dir Specification

## Scenarios

### native-build default output containment (task #35)

#### resolves a missing -o/--output to build/native/<entry-stem>

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a missing -o/--output to build/native/<entry-stem>
   - Expected: stem equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a missing -o/--output to build/native/<entry-stem>")
# The resolver formula, verified in place (not called -- see header).
val body = _resolver_body()
expect(body).to_contain("build/native/{{_cli_native_build_stem(entry_point)}}")
# The rfind-based primitive the formula is built from, verified for
# real against the exact shape the resolver uses (no std.path).
val entry = "src/app/cli/main.spl"
val slash = entry.rfind("/")
val base = if slash >= 0: entry.substring(slash + 1) else: entry
val dot = base.rfind(".")
val stem = if dot > 0: base.substring(0, dot) else: base
expect(stem).to_equal("main")
```

</details>

#### never falls back to the bare a.out literal in the resolver

- never falls back to the bare a.out literal in the resolver
   - Expected: body does not contain `"a.out"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never falls back to the bare a.out literal in the resolver")
val body = _resolver_body()
expect(body.contains("\"a.out\"")).to_equal(false)
```

</details>

#### returns an explicit -o/--output unchanged

- returns an explicit -o/--output unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an explicit -o/--output unchanged")
val body = _resolver_body()
expect(body).to_contain("if output_explicit:")
expect(body).to_contain("        output\n")
```

</details>

#### derives the launch-metadata sidecar from the resolved output, never cwd

- derives the launch-metadata sidecar from the resolved output, never cwd
   - Expected: launch_metadata_sidecar_path("build/native/main") equals `build/native/main.simple_launch.sdn`
   - Expected: launch_metadata_sidecar_path("build/native/main").starts_with("build/native/") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the launch-metadata sidecar from the resolved output, never cwd")
expect(launch_metadata_sidecar_path("build/native/main")).to_equal("build/native/main.simple_launch.sdn")
expect(launch_metadata_sidecar_path("build/native/main").starts_with("build/native/")).to_equal(true)
```

</details>

#### derives the native-build staging and assembly sidecars from the resolved output

- derives the native-build staging and assembly sidecars from the resolved output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the native-build staging and assembly sidecars from the resolved output")
val compile_src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(compile_src).to_contain("val staged_output = \"{{output}}.simple-native-build-{{getpid()}}-{{time_now_unix_micros()}}.tmp\"")
val mold_src = file_read("src/compiler/70.backend/linker/mold.spl")
expect(mold_src).to_contain("val asm_path = output_path + \".s\"")
```

</details>

#### creates the resolved output's parent directory unconditionally

- creates the resolved output's parent directory unconditionally
   - Expected: "out".rfind("/") > 0 is false
   - Expected: "build/native/main".rfind("/") > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates the resolved output's parent directory unconditionally")
# A bare filename's parent is "." (a safe no-op create); a nested
# default path's parent is the build/native tree that must exist
# before the compiler writes into it. Uses the same raw rfind +
# `> 0` idiom as the stem helper, not std.path.dirname.
expect("out".rfind("/") > 0).to_equal(false)
expect("build/native/main".rfind("/") > 0).to_equal(true)
val compile_src = file_read("src/app/io/_CliCompile/compile_targets.spl")
expect(compile_src).to_contain("val out_parent = if out_slash > 0: output.substring(0, out_slash) else: \".\"")
expect(compile_src).to_contain("if not _cli_dir_create_impl(out_parent, true):")
```

</details>

#### keeps the LinkConfig struct default contained under build/native/ too

- keeps the LinkConfig struct default contained under build/native/ too
   - Expected: link_src does not contain `output_path: "a.out"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the LinkConfig struct default contained under build/native/ too")
val link_src = file_read("src/compiler/70.backend/linker/link.spl")
expect(link_src).to_contain("output_path: \"build/native/a.out\"")
expect(link_src.contains("output_path: \"a.out\"")).to_equal(false)
```

</details>

#### avoids std.path.stem/dirname in every sibling default-output site (native-codegen trap)

- avoids std.path.stem/dirname in every sibling default-output site (native-codegen trap)
   - Expected: src does not contain `use std.path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("avoids std.path.stem/dirname in every sibling default-output site (native-codegen trap)")
# See header: std.path's Option-match on a raw rfind i64 crashes
# under native MIR codegen. Every site this lane touches must use the
# local rfind-based helper instead, not `use std.path`.
val sites = [
    "src/app/io/_CliCompile/compile_targets.spl",
    "src/app/io/_CliCompile/compile_opt_and_driver.spl",
    "src/app/cli/bootstrap_main.spl",
    "src/compiler/80.driver/driver_aot_pipeline.spl",
    "src/compiler/80.driver/driver_types.spl",
    "src/compiler/80.driver/main.spl"
]
for site in sites:
    val src = file_read(site)
    expect(src.contains("use std.path")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/default_output_dir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering native-build default output containment (task #35).
- native-build default output containment (task #35)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `bb58d9b35b1352e18c21d811f3011a3a7eafe5dc0651829d36c2cc300a940c15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb58d9b35b1352e18c21d811f3011a3a7eafe5dc0651829d36c2cc300a940c15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb58d9b35b1352e18c21d811f3011a3a7eafe5dc0651829d36c2cc300a940c15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/cli/default_output_dir_spec.spl
mirror: doc/06_spec/01_unit/app/cli/default_output_dir_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/default_output_dir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/default_output_dir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/default_output_dir_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves a missing -o/--output to build/native/<entry-stem>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/default_output_dir_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never falls back to the bare a.out literal in the resolver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/default_output_dir_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an explicit -o/--output unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
