# simpleos_guest_toolchain_wrapper_spec

> Host-fixture coverage for the production SimpleOS guest toolchain wrapper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_guest_toolchain_wrapper_spec

Host-fixture coverage for the production SimpleOS guest toolchain wrapper.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Host-fixture coverage for the production SimpleOS guest toolchain wrapper.

These scenarios execute scripts/simpleos_guest_toolchain_wrapper.shs with
controlled payload fixtures. They prove dispatch, target reporting, and
fail-closed no-host-fallback behavior. They do not prove that a payload ran in
SimpleOS and cannot satisfy live deployment or desktop acceptance.

## Scenarios

### SimpleOS guest toolchain wrapper

#### should report clang guest status and forward supported LLVM operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should report clang guest status and forward supported LLVM operations
- Create an isolated guest-wrapper fixture
- Query the production clang wrapper status and target
   - Expected: triple_out.trim() equals `x86_64-simpleos`
- Forward compile and link operations to the staged LLVM payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report clang guest status and forward supported LLVM operations")
step("Create an isolated guest-wrapper fixture")
val tmpdir = setup_wrapper_fixture()

step("Query the production clang wrapper status and target")
val status_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' --print simpleos-wrapper-status"
val (status_out, status_err, status_code) = run_shell(status_cmd)
if status_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang status command failed: {status_out}{status_err}")
expect(status_out).to_contain("lane=x86_64-simpleos")
expect(status_out).to_contain("mode=native-wrapper")
expect(status_out).to_contain("status=guest-exec")

val triple_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' --print-target-triple"
val (triple_out, triple_err, triple_code) = run_shell(triple_cmd)
if triple_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang triple command failed: {triple_out}{triple_err}")
expect(triple_out.trim()).to_equal("x86_64-simpleos")

step("Forward compile and link operations to the staged LLVM payloads")
val exec_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/clang' -c /tmp/hello.c -o /tmp/hello.o"
val (exec_out, exec_err, exec_code) = run_shell(exec_cmd)
if exec_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("clang exec command failed: {exec_out}{exec_err}")
expect(exec_out).to_contain("LLVM_PAYLOAD -c /tmp/hello.c -o /tmp/hello.o")

val link_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/ld.lld' /tmp/hello.o -o /tmp/hello.elf"
val (link_out, link_err, link_code) = run_shell(link_cmd)
cleanup_tmpdir(tmpdir)
if link_code != 0:
    fail("ld.lld exec command failed: {link_out}{link_err}")
expect(link_out).to_contain("LLD_PAYLOAD /tmp/hello.o -o /tmp/hello.elf")
```

</details>

#### should expose the supported CMake and Ninja configure lane

- should expose the supported CMake and Ninja configure lane
- Create an isolated configure-wrapper fixture
- Query production CMake wrapper capabilities
- Generate Ninja commands with stable guest tool paths
- Forward Ninja execution to the staged payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose the supported CMake and Ninja configure lane")
step("Create an isolated configure-wrapper fixture")
val tmpdir = setup_wrapper_fixture()

step("Query production CMake wrapper capabilities")
val caps_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cmake' -E capabilities"
val (caps_out, caps_err, caps_code) = run_shell(caps_cmd)
if caps_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("cmake capabilities failed: {caps_out}{caps_err}")
expect(caps_out).to_contain("serverMode=false")
expect(caps_out).to_contain("lane=x86_64-simpleos")
expect(caps_out).to_contain("status=report-and-gate")

step("Generate Ninja commands with stable guest tool paths")
val cfg_cmd =
    "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cmake' " +
    "-S '{tmpdir}/src' -B '{tmpdir}/build' -G Ninja"
val (cfg_out, cfg_err, cfg_code) = run_shell(cfg_cmd)
if cfg_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("cmake configure failed: {cfg_out}{cfg_err}")
expect(cfg_out).to_contain("Build files have been written to: {tmpdir}/build")

val ninja_file_cmd =
    "grep -q '/usr/bin/clang' '{tmpdir}/build/build.ninja' && " +
    "grep -q '/usr/bin/ld.lld' '{tmpdir}/build/build.ninja'"
val (_, _, ninja_file_code) = run_shell(ninja_file_cmd)
if ninja_file_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("generated build.ninja does not reference the stable guest tool paths")

step("Forward Ninja execution to the staged payload")
val ninja_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/ninja' -C '{tmpdir}/build'"
val (ninja_out, ninja_err, ninja_code) = run_shell(ninja_cmd)
cleanup_tmpdir(tmpdir)
if ninja_code != 0:
    fail("ninja wrapper failed: {ninja_out}{ninja_err}")
expect(ninja_out).to_contain("NINJA_PAYLOAD -C {tmpdir}/build")
```

</details>

#### should expose Rust discovery and reject unsupported build operations

- should expose Rust discovery and reject unsupported build operations
- Create an isolated report-and-gate wrapper fixture
- Query the production Rust wrapper discovery surface
   - Expected: target_out.trim() equals `/usr/lib/rustlib/x86_64-unknown-simpleos/lib`
- Reject unsupported Rust compilation without host fallback
   - Expected: rust_fail_code equals `1`
- Reject unsupported Cargo builds without host fallback
   - Expected: cargo_fail_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose Rust discovery and reject unsupported build operations")
step("Create an isolated report-and-gate wrapper fixture")
val tmpdir = setup_wrapper_fixture()

step("Query the production Rust wrapper discovery surface")
val status_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' --print simpleos-wrapper-status"
val (status_out, status_err, status_code) = run_shell(status_cmd)
if status_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("rustc status failed: {status_out}{status_err}")
expect(status_out).to_contain("lane=x86_64-simpleos")
expect(status_out).to_contain("status=report-and-gate")

val target_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' --print target-libdir"
val (target_out, target_err, target_code) = run_shell(target_cmd)
if target_code != 0:
    cleanup_tmpdir(tmpdir)
    fail("rustc target-libdir failed: {target_out}{target_err}")
expect(target_out.trim()).to_equal("/usr/lib/rustlib/x86_64-unknown-simpleos/lib")

step("Reject unsupported Rust compilation without host fallback")
val rust_fail_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/rustc' main.rs"
val (_rust_fail_out, rust_fail_err, rust_fail_code) = run_shell(rust_fail_cmd)
expect(rust_fail_code).to_equal(1)
expect(rust_fail_err).to_contain("lane=x86_64-simpleos")
expect(rust_fail_err).to_contain("mode=native-wrapper")
expect(rust_fail_err).to_contain("status=report-and-gate")
expect(rust_fail_err).to_contain("no host fallback")

step("Reject unsupported Cargo builds without host fallback")
val cargo_fail_cmd = "SIMPLEOS_WRAPPER_ROOT='{tmpdir}' '{tmpdir}/work/bin/cargo' build"
val (_cargo_fail_out, cargo_fail_err, cargo_fail_code) = run_shell(cargo_fail_cmd)
cleanup_tmpdir(tmpdir)
expect(cargo_fail_code).to_equal(1)
expect(cargo_fail_err).to_contain("lane=x86_64-simpleos")
expect(cargo_fail_err).to_contain("status=report-and-gate")
expect(cargo_fail_err).to_contain("no host fallback")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `16b0b081dfcda3ecff3174df60513410865a355e8b78dbb12b98070000671e62`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `16b0b081dfcda3ecff3174df60513410865a355e8b78dbb12b98070000671e62`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `16b0b081dfcda3ecff3174df60513410865a355e8b78dbb12b98070000671e62`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_guest_toolchain_wrapper_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_guest_toolchain_wrapper_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_guest_toolchain_wrapper_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report clang guest status and forward supported LLVM operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report clang guest status and forward supported LLVM operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose the supported CMake and Ninja configure lane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose the supported CMake and Ninja configure lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:165:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose Rust discovery and reject unsupported build operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose Rust discovery and reject unsupported build operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
