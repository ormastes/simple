# Stage3 Real Entry Body Regression

> This fail-closed system spec proves that an admitted pure-Simple Stage3 can

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage3 Real Entry Body Regression

This fail-closed system spec proves that an admitted pure-Simple Stage3 can

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/bootstrap_stage3_real_body_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This fail-closed system spec proves that an admitted pure-Simple Stage3 can
compile and execute a nontrivial positional entry.  A link-valid ret-0 stub
cannot satisfy the runtime marker assertion.

## Scenarios

### pure-Simple Stage3 real entry body

#### builds and executes a nontrivial bare positional entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds and executes a nontrivial bare positional entry
- Require an explicit admitted pure-Simple Stage3 binary
   - Expected: rt_file_exists(stage3) is true
   - Expected: stage3 does not contain `src/compiler_rust`
- Verify the selected compiler identifies as the bootstrap compiler
   - Expected: version_code equals `0`
   - Expected: version_err equals ``
- Write a helper-calling entry whose observable marker requires real body execution
   - Expected: mkdir_code equals `0`
   - Expected: mkdir_out equals ``
   - Expected: rt_file_write_text(SOURCE_PATH, probe_source()) is true
- Build through Stage3 using the canonical bare positional entry form
   - Expected: build_code equals `0`
   - Expected: build_err equals ``
   - Expected: rt_file_exists(NATIVE_PATH) is true
- Execute the artifact and reject a link-valid ret-0 stub
   - Expected: run_code equals `0`
   - Expected: run_err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds and executes a nontrivial bare positional entry")
val stage3 = rt_env_get("SIMPLE_STAGE3_BIN") ?? ""

step("Require an explicit admitted pure-Simple Stage3 binary")
expect(stage3.len()).to_be_greater_than(0)
expect(rt_file_exists(stage3)).to_equal(true)
expect(stage3.contains("src/compiler_rust")).to_equal(false)

step("Verify the selected compiler identifies as the bootstrap compiler")
val (version_out, version_err, version_code) = rt_process_run(stage3, ["--version"])
expect(version_code).to_equal(0)
expect(version_err).to_equal("")
expect(version_out).to_contain("simple-bootstrap 1.0.0-RC")

step("Write a helper-calling entry whose observable marker requires real body execution")
val (mkdir_out, mkdir_code) = shell("rm -rf '" + BUILD_DIR + "' && mkdir -p '" + BUILD_DIR + "'")
expect(mkdir_code).to_equal(0)
expect(mkdir_out).to_equal("")
expect(rt_file_write_text(SOURCE_PATH, probe_source())).to_equal(true)

step("Build through Stage3 using the canonical bare positional entry form")
val (build_out, build_err, build_code) = rt_process_run("/usr/bin/env", [
    "-u", "SIMPLE_BOOTSTRAP",
    "-u", "SIMPLE_RUNTIME_PATH",
    "SIMPLE_NO_STUB_FALLBACK=1",
    "SIMPLE_LIB=src",
    stage3,
    "native-build",
    "--backend", "cranelift",
    "--entry-closure",
    "--cache-dir", CACHE_DIR,
    "--output", NATIVE_PATH,
    SOURCE_PATH
])
expect(build_code).to_equal(0)
expect(build_err).to_equal("")
expect(rt_file_exists(NATIVE_PATH)).to_equal(true)

step("Execute the artifact and reject a link-valid ret-0 stub")
val (run_out, run_err, run_code) = rt_process_run(NATIVE_PATH, [])
expect(run_code).to_equal(0)
expect(run_err).to_equal("")
expect(run_out).to_contain(MARKER)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e3ef86f1f175f11a14b7113c0c40864c77425ba55290414637eb46c950f68668`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3ef86f1f175f11a14b7113c0c40864c77425ba55290414637eb46c950f68668`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3ef86f1f175f11a14b7113c0c40864c77425ba55290414637eb46c950f68668`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/compiler/bootstrap_stage3_real_body_spec.spl
mirror: doc/06_spec/03_system/compiler/bootstrap_stage3_real_body_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/bootstrap_stage3_real_body_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/bootstrap_stage3_real_body_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/bootstrap_stage3_real_body_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/bootstrap_stage3_real_body_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds and executes a nontrivial bare positional entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
