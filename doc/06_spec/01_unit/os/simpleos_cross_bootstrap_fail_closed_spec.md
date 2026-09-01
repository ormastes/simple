# simpleos_cross_bootstrap_fail_closed_spec

> Regression contract for the SimpleOS cross-bootstrap stage builder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_cross_bootstrap_fail_closed_spec

Regression contract for the SimpleOS cross-bootstrap stage builder.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression contract for the SimpleOS cross-bootstrap stage builder.

The lane must produce target-native compiler artifacts, retain its per-stage
cache, and reject unresolved-symbol stub generation. A host seed wrapper is
not a SimpleOS compiler and must never be emitted as a bootstrap stage.

## Scenarios

### SimpleOS cross-bootstrap is target-bound and fail-closed

#### keeps bootstrap compilers host-runnable and disables stub fallback

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps bootstrap compilers host-runnable and disables stub fallback
   - Expected: source does not contain ` --target " + "{" + "config.target}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps bootstrap compilers host-runnable and disables stub fallback")
val source = file_read(STAGES)
expect(source.contains(" --target " + "{" + "config.target}")).to_equal(false)
expect(source).to_contain("process.run(output, [\"--version\"])")
expect(source).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
```

</details>

#### preserves an isolated cache for every stage

- preserves an isolated cache for every stage
   - Expected: source does not contain `" --clean"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves an isolated cache for every stage")
val source = file_read(STAGES)
expect(source).to_contain("/host-tools/stage" + "{" + "stage}/native-cache")
expect(source).to_contain(" --cache-dir " + "{" + "cache_dir}")
expect(source.contains("\" --clean\"")).to_equal(false)
```

</details>

#### contains no seed-wrapper bootstrap fallback

- contains no seed-wrapper bootstrap fallback
   - Expected: source does not contain `emit_stage_seed_wrapper`
   - Expected: source does not contain `seed_wrapper.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("contains no seed-wrapper bootstrap fallback")
val source = file_read(CONFIG)
expect(source.contains("emit_stage_seed_wrapper")).to_equal(false)
expect(source.contains("seed_wrapper.c")).to_equal(false)
```

</details>

#### separates target artifacts and fails closed before packaging

- separates target artifacts and fails closed before packaging


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("separates target artifacts and fails closed before packaging")
val config = file_read(CONFIG)
val stages = file_read(STAGES)
expect(config).to_contain("fn target_artifact_path")
expect(config).to_contain("/target/stage")
expect(stages).to_contain("host bootstrap compilers cannot be installed into SimpleOS")
```

</details>

#### builds the host seed before stage 1 and never executes the target seed

- builds the host seed before stage 1 and never executes the target seed


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("builds the host seed before stage 1 and never executes the target seed")
val config = file_read(CONFIG)
val stages = file_read(STAGES)
expect(config).to_contain("fn host_seed_output_path")
expect(config).to_contain("fn target_seed_output_path")
expect(config).to_contain("fn build_host_seed")
expect(config).to_contain("fn build_target_seed")
expect(config).to_contain("{" + "RUST_SEED_DIR}/target/bootstrap/simple")
expect(config).to_contain("Ready at " + "{" + "output} (not host-executed)")
expect(config).to_contain("process.run(\"file\", [supplied])")
expect(config).to_contain("host_seed_identity_matches(")
val host_seed_build = stages.index_of("build_host_seed(config)")
val stage1_build = stages.index_of("build_stage_cross_with_retry(config, 1, seed)")
val target_seed_build = stages.index_of("build_target_seed(config)")
expect(host_seed_build).to_be_greater_than(-1)
expect(stage1_build).to_be_greater_than(host_seed_build)
expect(target_seed_build).to_be_greater_than(stage1_build)
```

</details>

#### propagates package failure and advertises only a published archive

- propagates package failure and advertises only a published archive
   - Expected: stages does not contain `print "WARNING: Packaging failed"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("propagates package failure and advertises only a published archive")
val stages = file_read(STAGES)
expect(stages).to_contain("if not package_bootstrap(config):")
expect(stages).to_contain("print \"FAILED: Packaging failed\"")
expect(stages).to_contain("package_succeeded = true")
expect(stages).to_contain(
    "if package_succeeded and path_exists(config.archive_path()):")
expect(stages.contains("print \"WARNING: Packaging failed\"")).to_equal(false)
```

</details>

#### admits static host x86 and rejects dynamic foreign architectures

- admits static host x86 and rejects dynamic foreign architectures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("admits static host x86 and rejects dynamic foreign architectures")
expect(host_seed_identity_matches(
    "ELF 64-bit LSB executable, x86-64, statically linked",
    "Linux", "x86_64")).to_equal(true)
expect(host_seed_identity_matches(
    "ELF 64-bit LSB pie executable, ARM aarch64, dynamically linked",
    "Linux", "x86_64")).to_equal(false)
expect(host_seed_identity_matches(
    "ELF 64-bit LSB executable, UCB RISC-V, 64-bit, dynamically linked",
    "Linux", "x86_64")).to_equal(false)
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efb9e3211aac55365e72147673caf7d979615f7b9bf647a80882a8ff110e623f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efb9e3211aac55365e72147673caf7d979615f7b9bf647a80882a8ff110e623f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efb9e3211aac55365e72147673caf7d979615f7b9bf647a80882a8ff110e623f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps bootstrap compilers host-runnable and disables stub fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves an isolated cache for every stage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_cross_bootstrap_fail_closed_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'contains no seed-wrapper bootstrap fallback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
