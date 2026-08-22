# simple_app_startup_spec

> Verifies the simple app startup behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_app_startup_spec

Verifies the simple app startup behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the simple app startup behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### simple app startup metadata

### REQ-001: launch kind detection

#### should classify SMF files as SMF launches

- Verify: should classify SMF files as SMF launches
   - Expected: startup_detect_launch_kind("tool.smf") equals `smf`
   - Expected: startup_detect_launch_kind("TOOL.SMF") equals `smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should classify SMF files as SMF launches")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(startup_detect_launch_kind("tool.smf")).to_equal("smf")
expect(startup_detect_launch_kind("TOOL.SMF")).to_equal("smf")
```

</details>

#### should classify Simple source files as script launches

- Verify: should classify Simple source files as script launches
   - Expected: startup_detect_launch_kind("main.spl") equals `script`
   - Expected: startup_detect_launch_kind("run.shs") equals `script`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should classify Simple source files as script launches")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(startup_detect_launch_kind("main.spl")).to_equal("script")
expect(startup_detect_launch_kind("run.shs")).to_equal("script")
```

</details>

#### should classify other executable files as native launches

- Verify: should classify other executable files as native launches
   - Expected: startup_detect_launch_kind("simple") equals `native`
   - Expected: startup_detect_launch_kind("app.bin") equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should classify other executable files as native launches")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(startup_detect_launch_kind("simple")).to_equal("native")
expect(startup_detect_launch_kind("app.bin")).to_equal("native")
```

</details>

### REQ-002: file argument parsing

#### should add the entry path as argv zero when missing

- Verify: should add the entry path as argv zero when missing
   - Expected: args[0] equals `main.spl`
   - Expected: args[1] equals `one`
   - Expected: args[2] equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should add the entry path as argv zero when missing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val args = startup_normalize_program_args("main.spl", ["one", "two"])
expect(args[0]).to_equal("main.spl")
expect(args[1]).to_equal("one")
expect(args[2]).to_equal("two")
```

</details>

#### should not duplicate argv zero when caller already passed it

- Verify: should not duplicate argv zero when caller already passed it
   - Expected: args.len() equals `2)  # oracle: pinned constant asserted by this scenario`
   - Expected: args[0] equals `main.spl`
   - Expected: args[1] equals `one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should not duplicate argv zero when caller already passed it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val args = startup_normalize_program_args("main.spl", ["main.spl", "one"])
expect(args.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario
expect(args[0]).to_equal("main.spl")
expect(args[1]).to_equal("one")
```

</details>

#### should exclude app arg parser code when metadata says the app does not use it

- Verify: should exclude app arg parser code when metadata says the app does not use it
   - Expected: plan.include_arg_parser is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should exclude app arg parser code when metadata says the app does not use it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("native", false, false, [], [])
val plan = startup_plan_from_metadata("native_app", ["--unused"], metadata, true, false)
expect(plan.include_arg_parser).to_equal(false)
expect(startup_feature_summary(plan)).to_contain("arg_parser=false")
```

</details>

### REQ-003: mmap or cache strategy

#### should use host mmap when metadata requests cache and host supports mmap

- Verify: should use host mmap when metadata requests cache and host supports mmap
   - Expected: plan.executable_source equals `filesystem`
   - Expected: plan.include_mmap_cache is true
   - Expected: plan.cache_strategy equals `mmap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should use host mmap when metadata requests cache and host supports mmap")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("script", true, true, [], [])
val plan = startup_plan_from_metadata("main.spl", [], metadata, true, false)
expect(plan.executable_source).to_equal("filesystem")
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("mmap")
```

</details>

#### should use SimpleOS VFS prewarm when host mmap is unavailable

- Verify: should use SimpleOS VFS prewarm when host mmap is unavailable
   - Expected: plan.include_mmap_cache is true
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should use SimpleOS VFS prewarm when host mmap is unavailable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("smf", true, true, [], [])
val plan = startup_plan_from_metadata("app.smf", [], metadata, false, true)
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
```

</details>

#### should make SimpleOS app metadata use the SimpleOS VFS prewarm lane

- Verify: should make SimpleOS app metadata use the SimpleOS VFS prewarm lane
   - Expected: plan.target_os equals `simpleos`
   - Expected: plan.include_mmap_cache is true
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should make SimpleOS app metadata use the SimpleOS VFS prewarm lane")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = launch_metadata_for_simpleos_path("/sys/apps/simple.smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(startup_feature_summary(plan)).to_contain("os=simpleos")
```

</details>

#### should fall back to normal read when no cache support is available

- Verify: should fall back to normal read when no cache support is available
   - Expected: plan.include_mmap_cache is false
   - Expected: plan.cache_strategy equals `normal_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should fall back to normal read when no cache support is available")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("script", true, true, [], [])
val plan = startup_plan_from_metadata("main.spl", [], metadata, false, false)
expect(plan.include_mmap_cache).to_equal(false)
expect(plan.cache_strategy).to_equal("normal_read")
```

</details>

### REQ-004: conditional dynlib loading

#### should include no dynlib loader when no dependencies are declared

- Verify: should include no dynlib loader when no dependencies are declared
   - Expected: plan.include_dynlib_loader is false
   - Expected: plan.load_native_dynlibs.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: plan.load_smf_dynlibs.len() equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should include no dynlib loader when no dependencies are declared")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("native", false, false, [], [])
val plan = startup_plan_from_metadata("native_app", [], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(false)
expect(plan.load_native_dynlibs.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(plan.load_smf_dynlibs.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should load native dynlibs declared by native build metadata

- Verify: should load native dynlibs declared by native build metadata
   - Expected: plan.include_dynlib_loader is true
   - Expected: plan.load_native_dynlibs[0] equals `libsimple_gui.dylib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should load native dynlibs declared by native build metadata")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("native", false, false, ["libsimple_gui.dylib"], [])
val plan = startup_plan_from_metadata("native_app", [], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_native_dynlibs[0]).to_equal("libsimple_gui.dylib")
```

</details>

#### should load SMF dynlibs declared by SMF metadata

- Verify: should load SMF dynlibs declared by SMF metadata
   - Expected: plan.include_dynlib_loader is true
   - Expected: plan.load_smf_dynlibs[0] equals `/sys/lib/gui_hot.smf`
   - Expected: plan.program_args[0] equals `app.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should load SMF dynlibs declared by SMF metadata")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = _metadata("smf", true, true, [], ["/sys/lib/gui_hot.smf"])
val plan = startup_plan_from_metadata("app.smf", ["app.smf"], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.program_args[0]).to_equal("app.smf")
```

</details>

### REQ-005: build launch metadata sidecar

#### should render native build launch metadata as a sidecar

- Verify: should render native build launch metadata as a sidecar


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should render native build launch metadata as a sidecar")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = launch_metadata_for_native_build("host", "x86_64", "native")
val sidecar = render_launch_metadata_sidecar(metadata)
expect(sidecar).to_contain("simple_launch_metadata:")
expect(sidecar).to_contain("entry_kind: \"native\"")
expect(sidecar).to_contain("uses_arg_parser: false")
expect(sidecar).to_contain("mmap_hint: false")
```

</details>

#### should parse sidecar metadata with native and SMF dynlib dependencies

- Verify: should parse sidecar metadata with native and SMF dynlib dependencies
   - Expected: metadata.entry_kind equals `smf`
   - Expected: metadata.target_os equals `simpleos`
   - Expected: plan.include_dynlib_loader is true
   - Expected: plan.load_native_dynlibs[0] equals `libhost_gui.dylib`
   - Expected: plan.load_smf_dynlibs[0] equals `/sys/lib/gui_hot.smf`
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should parse sidecar metadata with native and SMF dynlib dependencies")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val sidecar =
    "simple_launch_metadata:\n" +
    "  entry_kind: \"smf\"\n" +
    "  target_os: \"simpleos\"\n" +
    "  target_arch: \"x86_64\"\n" +
    "  target_abi: \"simpleos\"\n" +
    "  uses_arg_parser: true\n" +
    "  mmap_hint: true\n" +
    "  native_dynlib: \"libhost_gui.dylib\"\n" +
    "  smf_dynlib: \"/sys/lib/gui_hot.smf\"\n"
val metadata = parse_launch_metadata_sidecar(sidecar, "native")
val plan = startup_plan_from_metadata("app.smf", ["app.smf"], metadata, false, true)
expect(metadata.entry_kind).to_equal("smf")
expect(metadata.target_os).to_equal("simpleos")
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_native_dynlibs[0]).to_equal("libhost_gui.dylib")
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
```

</details>

#### should name sidecars next to the artifact path

- Verify: should name sidecars next to the artifact path
   - Expected: launch_metadata_sidecar_path("build/app") equals `build/app.simple_launch.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should name sidecars next to the artifact path")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(launch_metadata_sidecar_path("build/app")).to_equal("build/app.simple_launch.sdn")
```

</details>

### REQ-006: embedded SMF launch metadata

#### should parse embedded SMF metadata for SimpleOS startup

- Verify: should parse embedded SMF metadata for SimpleOS startup
   - Expected: metadata.entry_kind equals `smf`
   - Expected: metadata.target_os equals `simpleos`
   - Expected: plan.include_arg_parser is true
   - Expected: plan.include_mmap_cache is true
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`
   - Expected: plan.include_dynlib_loader is true
   - Expected: plan.load_smf_dynlibs[0] equals `/sys/lib/gui_hot.smf`
   - Expected: plan.program_args[0] equals `/sys/apps/simple.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should parse embedded SMF metadata for SimpleOS startup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var opts = SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu())
val sidecar =
    "simple_launch_metadata:\n" +
    "  entry_kind: \"smf\"\n" +
    "  target_os: \"simpleos\"\n" +
    "  target_arch: \"multiarch\"\n" +
    "  target_abi: \"simpleos\"\n" +
    "  uses_arg_parser: true\n" +
    "  mmap_hint: true\n" +
    "  smf_dynlib: \"/sys/lib/gui_hot.smf\"\n"
opts.launch_metadata_bytes = sidecar.bytes()

val smf = generate_smf_with_options([0xC3], opts)
val metadata = parse_launch_metadata_from_smf_bytes(smf, "smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", ["--open", "doc.spl"], metadata, false, true)

expect(metadata.entry_kind).to_equal("smf")
expect(metadata.target_os).to_equal("simpleos")
expect(plan.include_arg_parser).to_equal(true)
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.program_args[0]).to_equal("/sys/apps/simple.smf")
```

</details>

### REQ-007: embedded native launch metadata

#### should parse native launch metadata from the binary trailer

- Verify: should parse native launch metadata from the binary trailer
   - Expected: has_native_launch_metadata_trailer(binary) is true
   - Expected: parsed.entry_kind equals `native`
   - Expected: parsed.target_os equals `macos`
   - Expected: parsed.target_arch equals `aarch64`
   - Expected: parsed.target_abi equals `macho`
   - Expected: plan.include_arg_parser is false
   - Expected: plan.include_mmap_cache is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005 REQ-006 REQ-007
step("Verify: should parse native launch metadata from the binary trailer")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val metadata = launch_metadata_for_native_build("macos", "aarch64", "macho")
val binary = [0xCF, 0xFA, 0xED, 0xFE].concat(render_native_launch_metadata_trailer(metadata))
val parsed = parse_launch_metadata_from_native_bytes(binary, "native")
val plan = startup_plan_from_metadata("build/app", [], parsed, true, false)

expect(has_native_launch_metadata_trailer(binary)).to_equal(true)
expect(parsed.entry_kind).to_equal("native")
expect(parsed.target_os).to_equal("macos")
expect(parsed.target_arch).to_equal("aarch64")
expect(parsed.target_abi).to_equal("macho")
expect(plan.include_arg_parser).to_equal(false)
expect(plan.include_mmap_cache).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `448ba52962dd82dab0694e8c116583e7b85580ffc4e7e0e414e66d6fc96cbaae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `448ba52962dd82dab0694e8c116583e7b85580ffc4e7e0e414e66d6fc96cbaae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `448ba52962dd82dab0694e8c116583e7b85580ffc4e7e0e414e66d6fc96cbaae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/app/simple/feature/simple_app_startup_spec.spl
mirror: doc/06_spec/03_system/app/simple/feature/simple_app_startup_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple/feature/simple_app_startup_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/simple/feature/simple_app_startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple/feature/simple_app_startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify SMF files as SMF launches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify Simple source files as script launches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:69:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify other executable files as native launches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should add the entry path as argv zero when missing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not duplicate argv zero when caller already passed it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple/feature/simple_app_startup_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exclude app arg parser code when metadata says the app does not use it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
