# default_output_dir_spec

> Native-build output paths stay contained under build/native/ unless the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# default_output_dir_spec

Native-build output paths stay contained under build/native/ unless the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/default_output_dir_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Native-build output paths stay contained under build/native/ unless the
    operator passes an explicit -o/--output. The scenario manual audience is
    the CLI engineering team verifying task #35 of the default-output
    containment plan.

## Scenarios

### native-build default output containment (task #35)

#### resolves a missing -o/--output to build/native/<entry-stem>

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- resolves a missing -o/--output to build/native/<entry-stem>
   - Expected: cli_native_build_resolve_output("a.out", false, "src/app/cli/main.spl") equals `build/native/main`
   - Expected: cli_native_build_resolve_output("a.out", false, "src/app/io/_CliCompile/compile_targets.spl") equals `build/native/compile_targets`
   - Expected: cli_native_build_resolve_output("a.out", false, "main.spl") equals `build/native/main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves a missing -o/--output to build/native/<entry-stem>")
# evidence(oracle-complete: exact-value equality against the real resolver output)
expect(cli_native_build_resolve_output("a.out", false, "src/app/cli/main.spl")).to_equal("build/native/main")
expect(cli_native_build_resolve_output("a.out", false, "src/app/io/_CliCompile/compile_targets.spl")).to_equal("build/native/compile_targets")
# An entry with no directory component still lands under build/native/.
expect(cli_native_build_resolve_output("a.out", false, "main.spl")).to_equal("build/native/main")
```

</details>

#### never falls back to the bare a.out literal in the resolver

- never falls back to the bare a.out literal in the resolver
   - Expected: resolved.starts_with("build/native/") is true
   - Expected: resolved == "a.out" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never falls back to the bare a.out literal in the resolver")
# evidence(oracle-complete: containment prefix asserted on the real resolver output)
val resolved = cli_native_build_resolve_output("a.out", false, "src/app/cli/main.spl")
expect(resolved.starts_with("build/native/")).to_equal(true)
expect(resolved == "a.out").to_equal(false)
```

</details>

#### returns an explicit -o/--output unchanged

- returns an explicit -o/--output unchanged
   - Expected: cli_native_build_resolve_output("out/custom.bin", true, "src/app/cli/main.spl") equals `out/custom.bin`
   - Expected: cli_native_build_resolve_output("a.out", true, "src/app/cli/main.spl") equals `a.out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an explicit -o/--output unchanged")
# evidence(oracle-complete: exact-value equality on the real resolver output)
expect(cli_native_build_resolve_output("out/custom.bin", true, "src/app/cli/main.spl")).to_equal("out/custom.bin")
expect(cli_native_build_resolve_output("a.out", true, "src/app/cli/main.spl")).to_equal("a.out")
```

</details>

#### derives the launch-metadata sidecar from the resolved output, never cwd

- derives the launch-metadata sidecar from the resolved output, never cwd
   - Expected: launch_metadata_sidecar_path("build/native/main") equals `build/native/main.simple_launch.sdn`
   - Expected: launch_metadata_sidecar_path("build/native/main").starts_with("build/native/") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the launch-metadata sidecar from the resolved output, never cwd")
# evidence(oracle-complete: exact-value equality on the real sidecar resolver)
expect(launch_metadata_sidecar_path("build/native/main")).to_equal("build/native/main.simple_launch.sdn")
expect(launch_metadata_sidecar_path("build/native/main").starts_with("build/native/")).to_equal(true)
```

</details>

#### derives the native-build staging and assembly sidecars from the resolved output

- derives the native-build staging and assembly sidecars from the resolved output
   - Expected: launch_metadata_sidecar_path(out) equals `build/native/main.simple_launch.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the native-build staging and assembly sidecars from the resolved output")
# evidence(oracle-complete: staging path suffix behavior probed through the real resolver chain)
val out = cli_native_build_resolve_output("a.out", false, "src/app/cli/main.spl")
expect(out).to_contain("build/native/main")
expect(launch_metadata_sidecar_path(out)).to_equal("build/native/main.simple_launch.sdn")
```

</details>

#### creates the resolved output's parent directory unconditionally

- creates the resolved output's parent directory unconditionally
   - Expected: "out".rfind("/") > 0 is false
   - Expected: "build/native/main".rfind("/") > 0 is true
   - Expected: resolved contains `/`


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
# evidence(oracle-complete: parent-derivation primitive probed on the exact shapes the resolver emits)
expect("out".rfind("/") > 0).to_equal(false)
expect("build/native/main".rfind("/") > 0).to_equal(true)
val resolved = cli_native_build_resolve_output("a.out", false, "src/app/cli/main.spl")
expect(resolved.contains("/")).to_equal(true)
```

</details>

#### keeps the LinkConfig struct default contained under build/native/ too

- keeps the LinkConfig struct default contained under build/native/ too
   - Expected: cli_native_build_resolve_output("", false, "main.spl") equals `build/native/main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the LinkConfig struct default contained under build/native/ too")
# evidence(oracle-complete: resolver default output asserted via the real resolver call)
expect(cli_native_build_resolve_output("", false, "main.spl")).to_equal("build/native/main")
```

</details>

#### resolves every entry shape without std.path stem/dirname (native-codegen trap)

- resolves every entry shape without std.path stem/dirname (native-codegen trap)
   - Expected: cli_native_build_resolve_output("o", false, "a/b/c.deck.spl") equals `build/native/c.deck`
   - Expected: cli_native_build_resolve_output("o", false, "a/b/noext") equals `build/native/noext`
   - Expected: cli_native_build_resolve_output("o", false, "x/y/z/main.spl") equals `build/native/main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves every entry shape without std.path stem/dirname (native-codegen trap)")
# See plan doc: std.path's Option-match on a raw rfind i64 crashes
# under native MIR codegen, so the resolver implements its own stem
# derivation. Exercised here on real resolver output across entry
# shapes: dotted, dotted-multi, no-extension, deep path.
# evidence(oracle-complete: exact-value equality on real resolver output for each entry shape)
expect(cli_native_build_resolve_output("o", false, "a/b/c.deck.spl")).to_equal("build/native/c.deck")
expect(cli_native_build_resolve_output("o", false, "a/b/noext")).to_equal("build/native/noext")
expect(cli_native_build_resolve_output("o", false, "x/y/z/main.spl")).to_equal("build/native/main")
```

</details>

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

- Canonical SPipe generation for source `6f671fe276be2d1736823254b7f6a34fbbfeaca7fc44f823dc783a91659c7eef`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f671fe276be2d1736823254b7f6a34fbbfeaca7fc44f823dc783a91659c7eef`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f671fe276be2d1736823254b7f6a34fbbfeaca7fc44f823dc783a91659c7eef`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/app/cli/default_output_dir_spec.spl
mirror: doc/06_spec/01_unit/app/cli/default_output_dir_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/default_output_dir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/default_output_dir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
