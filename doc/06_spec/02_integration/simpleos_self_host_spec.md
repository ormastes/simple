# SimpleOS Self-Host Chain Integration Test

> Verifies the end-to-end self-host chain: SimpleOS boots in QEMU, loads the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Self-Host Chain Integration Test

Verifies the end-to-end self-host chain: SimpleOS boots in QEMU, loads the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/simpleos_self_host_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# SimpleOS Self-Host Chain Integration Test

Verifies the end-to-end self-host chain: SimpleOS boots in QEMU, loads the
Simple compiler from initramfs, compiles a trivial program to a native
binary, and runs the output.

Status: RED PHASE. The kernel exec path (posix_spawn / fork+execve) is
deferred; `step_trivial_self_host` in `simpleos_smoke_init.spl` will emit
`TRIVIAL_SELFHOST_SKIP reason=no-exec` until the kernel gains user-process
spawn support. See `src/os/port/init/simpleos_smoke_init.spl` for the
in-guest implementation.

Two-layer test:
  (a) Hosted-callable layer (this file): exercises QEMU command
      construction and tag/path configuration for the self-host chain.
      Runs under `bin/simple test` in interpreter mode.
  (b) Full QEMU smoke: documented as a manual command at the bottom.
      Requires a built kernel + initramfs. The host orchestrator
      `src/os/port/e2e_verify.spl` greps for `TRIVIAL_SELFHOST_OK`.

@cover src/os/port/init/simpleos_smoke_init.spl 80%
@cover src/os/port/e2e_verify.spl 60%
@req REQ-SIMPLEOS-SELFHOST
@feature simpleos-self-host-chain
# tag: os, qemu, slow, self-host

## Scenarios

### SimpleOS self-host chain — QEMU configuration

<details>
<summary>Advanced: x86_64 target includes kernel and serial stdio</summary>

#### x86_64 target includes kernel and serial stdio _(slow)_

- Verify: x86_64 target includes kernel and serial stdio
   - Expected: cmd[0] equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: x86_64 target includes kernel and serial stdio")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val target = get_target(Architecture.X86_64)
val cmd = build_qemu_command(target)
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("stdio")
```

</details>


</details>

<details>
<summary>Advanced: x86_64 target uses q35 machine</summary>

#### x86_64 target uses q35 machine _(slow)_

- Verify: x86_64 target uses q35 machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: x86_64 target uses q35 machine")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val target = get_target(Architecture.X86_64)
val cmd = build_qemu_command(target)
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("q35")
```

</details>


</details>

### SimpleOS self-host chain — tag contract

<details>
<summary>Advanced: TAG_TRIVIAL_OK matches the expected tag format</summary>

#### TAG_TRIVIAL_OK matches the expected tag format _(slow)_

- Verify: TAG_TRIVIAL_OK matches the expected tag format
   - Expected: TAG_TRIVIAL_OK equals `TRIVIAL_SELFHOST_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: TAG_TRIVIAL_OK matches the expected tag format")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TAG_TRIVIAL_OK).to_equal("TRIVIAL_SELFHOST_OK")
```

</details>


</details>

<details>
<summary>Advanced: TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP</summary>

#### TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP _(slow)_

- Verify: TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TAG_TRIVIAL_SKIP).to_start_with("TRIVIAL_SELFHOST_SKIP")
```

</details>


</details>

<details>
<summary>Advanced: TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL</summary>

#### TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL _(slow)_

- Verify: TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TAG_TRIVIAL_FAIL).to_start_with("TRIVIAL_SELFHOST_FAIL")
```

</details>


</details>

### SimpleOS self-host chain — in-guest path contract

<details>
<summary>Advanced: simple compiler binary path is /bin/simple</summary>

#### simple compiler binary path is /bin/simple _(slow)_

- Verify: simple compiler binary path is /bin/simple
   - Expected: SIMPLE_BIN equals `/bin/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: simple compiler binary path is /bin/simple")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(SIMPLE_BIN).to_equal("/bin/simple")
```

</details>


</details>

<details>
<summary>Advanced: trivial source is written under /tmp/selfhost_test/</summary>

#### trivial source is written under /tmp/selfhost_test/ _(slow)_

- Verify: trivial source is written under /tmp/selfhost_test/


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: trivial source is written under /tmp/selfhost_test/")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TRIVIAL_SRC_FILE).to_start_with("/tmp/selfhost_test/")
expect(TRIVIAL_SRC_FILE).to_end_with(".spl")
```

</details>


</details>

<details>
<summary>Advanced: output binary path matches source directory</summary>

#### output binary path matches source directory _(slow)_

- Verify: output binary path matches source directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: output binary path matches source directory")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TRIVIAL_OUTPUT).to_start_with("/tmp/selfhost_test/")
```

</details>


</details>

<details>
<summary>Advanced: trivial program expected output is defined</summary>

#### trivial program expected output is defined _(slow)_

- Verify: trivial program expected output is defined
   - Expected: TRIVIAL_EXPECTED_OUTPUT equals `hello from self-host`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: trivial program expected output is defined")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TRIVIAL_EXPECTED_OUTPUT).to_equal("hello from self-host")
```

</details>


</details>

### SimpleOS self-host chain — native-build command

<details>
<summary>Advanced: native-build args include source and entry flags</summary>

#### native-build args include source and entry flags _(slow)_

- Verify: native-build args include source and entry flags


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: native-build args include source and entry flags")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val args: [text] = [
    "native-build",
    "--source", TRIVIAL_SRC_DIR,
    "--entry", TRIVIAL_SRC_FILE,
    "-o", TRIVIAL_OUTPUT,
]
expect(args).to_contain("native-build")
expect(args).to_contain("--source")
expect(args).to_contain("--entry")
expect(args).to_contain(TRIVIAL_SRC_FILE)
expect(args).to_contain("-o")
expect(args).to_contain(TRIVIAL_OUTPUT)
```

</details>


</details>

<details>
<summary>Advanced: entry file path ends with hello.spl</summary>

#### entry file path ends with hello.spl _(slow)_

- Verify: entry file path ends with hello.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: entry file path ends with hello.spl")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(TRIVIAL_SRC_FILE).to_end_with("hello.spl")
```

</details>


</details>

### SimpleOS self-host chain — e2e tag grep

<details>
<summary>Advanced: detects TRIVIAL_SELFHOST_OK in stdout</summary>

#### detects TRIVIAL_SELFHOST_OK in stdout _(slow)_

- Verify: detects TRIVIAL_SELFHOST_OK in stdout
   - Expected: stdout contains `TAG_TRIVIAL_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: detects TRIVIAL_SELFHOST_OK in stdout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val stdout = "SIMPLEOS_SMOKE_INIT_STARTED\nTRIVIAL_SELFHOST_OK\nSIMPLEOS_SMOKE_INIT_DONE"
expect(stdout.contains(TAG_TRIVIAL_OK)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects TRIVIAL_SELFHOST_SKIP in stdout</summary>

#### detects TRIVIAL_SELFHOST_SKIP in stdout _(slow)_

- Verify: detects TRIVIAL_SELFHOST_SKIP in stdout
   - Expected: stdout contains `TAG_TRIVIAL_SKIP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: detects TRIVIAL_SELFHOST_SKIP in stdout")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val stdout = "TRIVIAL_SELFHOST_SKIP reason=no-exec\nSIMPLEOS_SMOKE_INIT_DONE"
expect(stdout.contains(TAG_TRIVIAL_SKIP)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns false when tag is absent</summary>

#### returns false when tag is absent _(slow)_

- Verify: returns false when tag is absent
   - Expected: stdout does not contain `TAG_TRIVIAL_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SIMPLEOS-SELFHOST
step("Verify: returns false when tag is absent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val stdout = "SIMPLEOS_SMOKE_INIT_STARTED\nSIMPLEOS_SMOKE_INIT_DONE"
expect(stdout.contains(TAG_TRIVIAL_OK)).to_equal(false)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 14 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e000d20ef261983688c704d89021dec95eb4785df89357ea499a57bec9f5419`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e000d20ef261983688c704d89021dec95eb4785df89357ea499a57bec9f5419`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e000d20ef261983688c704d89021dec95eb4785df89357ea499a57bec9f5419`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/simpleos_self_host_spec.spl
mirror: doc/06_spec/02_integration/simpleos_self_host_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/simpleos_self_host_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/simpleos_self_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/simpleos_self_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
