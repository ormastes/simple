# @req REQ-TESTRUNNER-SINGLE-LANE-NO-DROPPED-PATHS

> Neighbouring argv shapes the single-file lane must classify, not swallow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-TESTRUNNER-SINGLE-LANE-NO-DROPPED-PATHS

Neighbouring argv shapes the single-file lane must classify, not swallow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/single_lane_arg_parsing_neighbors_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Neighbouring argv shapes the single-file lane must classify, not swallow.

Audience: anyone editing `parse_child_run` in
`src/app/test_runner_new/test_runner_single.spl`.

Why this spec exists (GENERALIZATION). The defect closed on 2026-08-27 was one
instance of a class: a positional argument that the parser neither consumes nor
rejects, so the run proceeds as if it had never been asked for. This spec walks
the argv shapes adjacent to the reported one — extra paths interleaved between
flags, three paths, extra paths combined with `--timeout`, malformed option
values that could otherwise hide a path, and the several already-fail-closed
classes (missing path, non-`.spl`, nonexistent file) — and asserts each is
CLASSIFIED. Every shape here must land on a definite verdict:
either `valid: true` with the right path, or `valid: false` with a non-empty
error. Silence is the bug.

Record: doc/08_tracking/bug/test_runner_single_lane_drops_extra_paths_2026-08-27.md
Reproducer: test/01_unit/app/test_runner_new/single_lane_extra_paths_spec.spl

## Scenarios

### single-file lane argv classification

### extra paths in shapes adjacent to the reported one

#### refuses a second path hidden between flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--timeout", "60", SPEC_B, "--sequential"])
assert_false(run.valid)
```

</details>

#### refuses a second path when --timeout uses the = form

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--timeout=60", SPEC_B])
assert_false(run.valid)
```

</details>

#### refuses three paths and accounts for both extras

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, SPEC_B, SPEC_C])
assert_contains(run.error, "2 more")
```

</details>

#### refuses an extra path even when it is the same file twice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, SPEC_A])
assert_false(run.valid)
```

</details>

### already fail-closed classes stay fail-closed

#### rejects an argv with no path at all

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run(["--timeout", "60"])
assert_false(run.valid)
```

</details>

#### rejects a path that is not a .spl file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run(["test/01_unit/lib/std/common"])
assert_false(run.valid)
```

</details>

#### rejects a .spl path that does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run(["test/01_unit/lib/std/common/__absent_spec.spl"])
assert_false(run.valid)
```

</details>

#### never reports invalid without saying why

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, SPEC_B])
assert_not_equal(run.error, "")
```

</details>

### flag-only argv must not be mistaken for a path

#### still accepts one path when many flags surround it

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run(["--sequential", "--no-db", SPEC_A, "--no-cache"])
assert_true(run.valid)
```

</details>

#### keeps --list working on a single path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--list"])
assert_true(run.list_only)
```

</details>

### forwarded option values must not be mistaken for paths

#### accepts the separated --format value after the spec path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format", "json"])
assert_true(run.valid)
```

</details>

#### accepts the separated --format value before the spec path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run(["--format", "json", SPEC_A])
assert_true(run.valid)
```

</details>

#### accepts an adapter-forwarded QEMU socket value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--qemu-socket", "/tmp/simple-qemu.sock"])
assert_true(run.valid)
```

</details>

#### still refuses a real second path after a format value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format", "json", SPEC_B])
assert_false(run.valid)
```

</details>

#### fails closed when a value-taking option has no value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format"])
assert_false(run.valid)
assert_contains(run.error, "missing value for --format")
```

</details>

### malformed option values cannot hide another path

#### rejects a spec path used as an invalid --format value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "invalid value for --format")
```

</details>

#### does not swallow --list as the value of --format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format", "--list", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "missing value for --format")
```

</details>

#### rejects empty equals syntax before a second path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format=", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "missing value for --format")
```

</details>

#### rejects an invalid equals value before a second path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--format=yaml", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "invalid value for --format")
```

</details>

#### rejects a nonnumeric timeout before a second path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--timeout", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "invalid value for --timeout")
```

</details>

#### does not swallow --list as a QEMU socket value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--qemu-socket", "--list", SPEC_B])
assert_false(run.valid)
assert_contains(run.error, "missing value for --qemu-socket")
```

</details>

#### accepts a signed decimal threshold value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run = parse_child_run([SPEC_A, "--cpu-threshold", "-0.5"])
assert_true(run.valid)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
