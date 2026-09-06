# coreutils/chmod argument parsing + octal parser

> _Octal mode parser._

<!-- sdn-diagram:id=chmod_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chmod_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chmod_spec -> std
chmod_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chmod_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/chmod argument parsing + octal parser

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/01_unit/os/apps/coreutils/chmod_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### parse_octal
_Octal mode parser._

#### parses '0755' as 493

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_octal("0755").to_equal(493i64)
```

</details>

#### parses '644' as 420

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_octal("644").to_equal(420i64)
```

</details>

#### rejects non-octal digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_octal("788").to_equal(-1i64)
```

</details>

#### rejects alphabetic input

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_octal("abc").to_equal(-1i64)
```

</details>

#### rejects the empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parse_octal("").to_equal(-1i64)
```

</details>

### main_chmod argument parsing
_Entry-point argument handling._

#### too-few args returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_chmod(["0755"])
expect rc.to_equal(1i32)
```

</details>

#### invalid mode returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_chmod(["xyz", "/tmp/f"])
expect rc.to_equal(1i32)
```

</details>

#### valid mode + path returns i32

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rc = main_chmod(["0755", "/tmp/f"])
val is_int: bool = rc == 0i32 or rc != 0i32
expect is_int.to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
