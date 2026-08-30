# coreutils/kill argument parsing + signal parser

> _Signal-flag parsing._

<!-- sdn-diagram:id=kill_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kill_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kill_spec -> std
kill_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kill_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/kill argument parsing + signal parser

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/kill_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### parse_signal
_Signal-flag parsing._

#### -9 is SIGKILL

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("-9").to_equal(9i32)
```

</details>

#### -15 is SIGTERM

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("-15").to_equal(15i32)
```

</details>

#### -SIGINT is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("-SIGINT").to_equal(2i32)
```

</details>

#### -SIGTERM is 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("-SIGTERM").to_equal(15i32)
```

</details>

#### unknown signal returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("-BOGUS").to_equal(-1i32)
```

</details>

#### empty string returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("").to_equal(-1i32)
```

</details>

#### missing leading dash returns -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_signal("9").to_equal(-1i32)
```

</details>

### parse_pid
_Pid decimal parser._

#### parses '42' as 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_pid("42").to_equal(42i64)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_pid("").to_equal(-1i64)
```

</details>

#### rejects non-digit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_pid("abc").to_equal(-1i64)
```

</details>

### main_kill argument parsing
_Entry-point argument handling._

#### no args returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_kill([])
expect rc.to_equal(1i32)
```

</details>

#### --help returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_kill(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### only signal flag + missing pid returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_kill(["-9"])
expect rc.to_equal(1i32)
```

</details>

#### unknown signal returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_kill(["-FOO", "1"])
expect rc.to_equal(1i32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
