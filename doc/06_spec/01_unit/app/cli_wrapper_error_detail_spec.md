# CLI Wrapper Error Detail Regression Spec

> Regression guard for the release-binary error wrapper. The release binary

<!-- sdn-diagram:id=cli_wrapper_error_detail_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_wrapper_error_detail_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_wrapper_error_detail_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_wrapper_error_detail_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Wrapper Error Detail Regression Spec

Regression guard for the release-binary error wrapper. The release binary

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling / Error Reporting |
| Status | Active |
| Source | `test/01_unit/app/cli_wrapper_error_detail_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Bug ID:** B1 (compiler_bugs_for_crypto_2026-04-25.md)
**Memory:** feedback_simple_run_wrapper_broken.md
Regression guard for the release-binary error wrapper. The release binary
captures the bootstrap subprocess's stderr and re-emits it; the wrapper
must route through real stderr (not stdout with a "[STDERR]" prefix).

Acceptance per plan:
- stderr length > 50 bytes on a parse error
- stdout length == 0 on a parse error
- "[STDERR]" literal must NOT appear in stdout (across all error modes)

## Scenarios

### CLI wrapper error detail (B1)

#### parse error: stderr > 50 bytes, stdout == 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = _write_temp("parse", "fn main():\n    val x = {\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.len()).to_equal(0)
expect(stderr.len() > 50).to_equal(true)
```

</details>

#### parse error: '[STDERR]' literal must NOT appear in stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = _write_temp("parse_no_prefix", "fn main():\n    val x = {\n")
val (stdout, _, _) = _run_simple(script)
val _ = rt_file_delete(script)
expect(stdout.contains("[STDERR]")).to_equal(false)
```

</details>

#### runtime error: real message reaches stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = _write_temp("runtime", "fn main():\n    val x = 10\n    val y = 0\n    print x / y\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.contains("[STDERR]")).to_equal(false)
expect(stderr.len() > 0).to_equal(true)
```

</details>

#### semantic error: stderr carries the message; stdout has no '[STDERR]'

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Avoid f-string interpolation by using an unresolved function call
# rather than a `use foo.{bar}` import (the spec body is itself an
# interpolating string literal).
val script = _write_temp("semres", "fn main():\n    nonexistent_function_xyz()\n")
val (stdout, stderr, code) = _run_simple(script)
val _ = rt_file_delete(script)
expect(code).to_not_equal(0)
expect(stdout.contains("[STDERR]")).to_equal(false)
expect(stderr.len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
