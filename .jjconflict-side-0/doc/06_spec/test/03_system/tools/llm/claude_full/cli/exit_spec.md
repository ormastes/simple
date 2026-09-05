# Claude Full CLI Exit

> Checks centralized CLI exit result behavior.

<!-- sdn-diagram:id=exit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exit_spec -> std
exit_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI Exit

Checks centralized CLI exit result behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/exit_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks centralized CLI exit result behavior.

## Scenarios

### Claude full cli exit

#### models error exits

- Error writes optional stderr and exits 1
   - Expected: withMessage.code equals `cliErrorExitCode()`
   - Expected: withMessage.stderr equals `bad`
   - Expected: withMessage.stdout equals ``
   - Expected: withMessage.returnedNever is true
   - Expected: empty.stderr equals ``
   - Expected: empty.code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Error writes optional stderr and exits 1")
val withMessage = cliError("bad")
expect(withMessage.code).to_equal(cliErrorExitCode())
expect(withMessage.stderr).to_equal("bad")
expect(withMessage.stdout).to_equal("")
expect(withMessage.returnedNever).to_equal(true)
val empty = cliError("")
expect(empty.stderr).to_equal("")
expect(empty.code).to_equal(1)
```

</details>

#### models ok exits

- Ok writes optional stdout newline and exits 0
   - Expected: withMessage.code equals `cliOkExitCode()`
   - Expected: withMessage.stdout equals `done\n`
   - Expected: withMessage.stderr equals ``
   - Expected: cliOk("").stdout equals ``
   - Expected: cliOkAddsNewline() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ok writes optional stdout newline and exits 0")
val withMessage = cliOk("done")
expect(withMessage.code).to_equal(cliOkExitCode())
expect(withMessage.stdout).to_equal("done\n")
expect(withMessage.stderr).to_equal("")
expect(cliOk("").stdout).to_equal("")
expect(cliOkAddsNewline()).to_equal(true)
```

</details>

#### exports source-backed CLI exit notes

- Pin centralized output targets and test-spy contracts
   - Expected: cliErrorOutputTarget() equals `stderr`
   - Expected: cliOkOutputTarget() equals `stdout`
   - Expected: centralizedCliExitPoint() is true
   - Expected: processExitLintSuppressedHere() is true
   - Expected: testsSpyOnProcessExit() is true
   - Expected: testsSpyOnConsoleError() is true
   - Expected: testsSpyOnStdoutWrite() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin centralized output targets and test-spy contracts")
expect(cliErrorOutputTarget()).to_equal("stderr")
expect(cliOkOutputTarget()).to_equal("stdout")
expect(centralizedCliExitPoint()).to_equal(true)
expect(processExitLintSuppressedHere()).to_equal(true)
expect(testsSpyOnProcessExit()).to_equal(true)
expect(testsSpyOnConsoleError()).to_equal(true)
expect(testsSpyOnStdoutWrite()).to_equal(true)
expect(neverReturnTypePurpose()).to_contain("narrow control flow")
expect(copiedHandlerBlockReplaced()).to_contain("exit")
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
