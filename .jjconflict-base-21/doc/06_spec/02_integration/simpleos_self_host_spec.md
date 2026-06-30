# SimpleOS Self-Host Chain Integration Test

> Verifies the end-to-end self-host chain: SimpleOS boots in QEMU, loads the

<!-- sdn-diagram:id=simpleos_self_host_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_self_host_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_self_host_spec -> std
simpleos_self_host_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_self_host_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### SimpleOS self-host chain — QEMU configuration

<details>
<summary>Advanced: x86_64 target includes kernel and serial stdio</summary>

#### x86_64 target includes kernel and serial stdio _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TAG_TRIVIAL_OK).to_equal("TRIVIAL_SELFHOST_OK")
```

</details>


</details>

<details>
<summary>Advanced: TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP</summary>

#### TAG_TRIVIAL_SKIP starts with TRIVIAL_SELFHOST_SKIP _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TAG_TRIVIAL_SKIP).to_start_with("TRIVIAL_SELFHOST_SKIP")
```

</details>


</details>

<details>
<summary>Advanced: TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL</summary>

#### TAG_TRIVIAL_FAIL starts with TRIVIAL_SELFHOST_FAIL _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TAG_TRIVIAL_FAIL).to_start_with("TRIVIAL_SELFHOST_FAIL")
```

</details>


</details>

### SimpleOS self-host chain — in-guest path contract

<details>
<summary>Advanced: simple compiler binary path is /bin/simple</summary>

#### simple compiler binary path is /bin/simple _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SIMPLE_BIN).to_equal("/bin/simple")
```

</details>


</details>

<details>
<summary>Advanced: trivial source is written under /tmp/selfhost_test/</summary>

#### trivial source is written under /tmp/selfhost_test/ _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRIVIAL_SRC_FILE).to_start_with("/tmp/selfhost_test/")
expect(TRIVIAL_SRC_FILE).to_end_with(".spl")
```

</details>


</details>

<details>
<summary>Advanced: output binary path matches source directory</summary>

#### output binary path matches source directory _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRIVIAL_OUTPUT).to_start_with("/tmp/selfhost_test/")
```

</details>


</details>

<details>
<summary>Advanced: trivial program expected output is defined</summary>

#### trivial program expected output is defined _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRIVIAL_EXPECTED_OUTPUT).to_equal("hello from self-host")
```

</details>


</details>

### SimpleOS self-host chain — native-build command

<details>
<summary>Advanced: native-build args include source and entry flags</summary>

#### native-build args include source and entry flags _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TRIVIAL_SRC_FILE).to_end_with("hello.spl")
```

</details>


</details>

### SimpleOS self-host chain — e2e tag grep

<details>
<summary>Advanced: detects TRIVIAL_SELFHOST_OK in stdout</summary>

#### detects TRIVIAL_SELFHOST_OK in stdout _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stdout = "SIMPLEOS_SMOKE_INIT_STARTED\nTRIVIAL_SELFHOST_OK\nSIMPLEOS_SMOKE_INIT_DONE"
expect(stdout.contains(TAG_TRIVIAL_OK)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects TRIVIAL_SELFHOST_SKIP in stdout</summary>

#### detects TRIVIAL_SELFHOST_SKIP in stdout _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stdout = "TRIVIAL_SELFHOST_SKIP reason=no-exec\nSIMPLEOS_SMOKE_INIT_DONE"
expect(stdout.contains(TAG_TRIVIAL_SKIP)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns false when tag is absent</summary>

#### returns false when tag is absent _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
