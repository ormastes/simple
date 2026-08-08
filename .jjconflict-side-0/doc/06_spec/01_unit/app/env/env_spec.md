# Environment Config Unit Tests

> @cover src/lib/nogc_sync_mut/env/variables.spl 60%

<!-- sdn-diagram:id=env_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=env_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

env_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=env_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Environment Config Unit Tests

@cover src/lib/nogc_sync_mut/env/variables.spl 60%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-ENV-001 |
| Category | App \| Env |
| Status | Implemented |
| Source | `test/01_unit/app/env/env_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/env/variables.spl 60%
@cover src/lib/nogc_sync_mut/env/platform.spl 40%

## Scenarios

### Environment Variables

#### HOME is set and non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val home = env_val("HOME")
expect(home != "").to_equal(true)
expect(home.starts_with("/")).to_equal(true)
```

</details>

#### PATH is set and contains separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = env_val("PATH")
expect(path != "").to_equal(true)
expect(path.contains(":") or path.contains(";")).to_equal(true)
```

</details>

#### USER is set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val user = env_val("USER")
expect(user != "").to_equal(true)
expect(user.len() > 0).to_equal(true)
```

</details>

#### missing variable returns nil or empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = rt_env_get("__SIMPLE_TEST_NONEXISTENT_VAR_XYZ__")
val is_empty = missing == nil or missing == ""
expect(is_empty).to_equal(true)
```

</details>

#### set and read back a variable

1. rt env set
   - Expected: readback equals `hello42`
2. rt env remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("__SIMPLE_TEST_ENV_ROUND_TRIP__", "hello42")
val readback = env_val("__SIMPLE_TEST_ENV_ROUND_TRIP__")
expect(readback).to_equal("hello42")
rt_env_remove("__SIMPLE_TEST_ENV_ROUND_TRIP__")
```

</details>

#### remove clears a variable

1. rt env set
2. rt env remove
   - Expected: gone is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("__SIMPLE_TEST_ENV_REMOVE__", "present")
rt_env_remove("__SIMPLE_TEST_ENV_REMOVE__")
val after = rt_env_get("__SIMPLE_TEST_ENV_REMOVE__")
val gone = after == nil or after == ""
expect(gone).to_equal(true)
```

</details>

### Platform Detection

#### uname returns a known OS

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("/bin/sh", ["-c", "uname -s"])
val os_name = result[0].trim()
val code = result[2]
expect(code).to_equal(0)
val known = (os_name == "Linux" or os_name == "Darwin" or
    os_name == "FreeBSD" or os_name == "OpenBSD" or os_name == "NetBSD")
expect(known).to_equal(true)
```

</details>

#### uname -m returns a known architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = rt_process_run("/bin/sh", ["-c", "uname -m"])
val arch = result[0].trim()
val code = result[2]
expect(code).to_equal(0)
expect(arch.len() > 0).to_equal(true)
```

</details>

#### PWD or working directory is accessible

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pwd = env_val("PWD")
expect(pwd != "").to_equal(true)
expect(pwd.starts_with("/")).to_equal(true)
```

</details>

### Configuration Sources

#### env var set takes precedence over missing

1. rt env set
   - Expected: value equals `from_env`
2. rt env remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("__SIMPLE_TEST_PRIORITY__", "from_env")
val value = env_val("__SIMPLE_TEST_PRIORITY__")
expect(value).to_equal("from_env")
rt_env_remove("__SIMPLE_TEST_PRIORITY__")
```

</details>

#### missing env var falls back to default

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = rt_env_get("__SIMPLE_TEST_MISSING_CONFIG__")
val is_empty = raw == nil or raw == ""
expect(is_empty).to_equal(true)
val fallback = if is_empty: "default_value" else: raw
expect(fallback).to_equal("default_value")
```

</details>

#### overwrite replaces previous value

1. rt env set
2. rt env set
   - Expected: value equals `second`
3. rt env remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("__SIMPLE_TEST_OVERWRITE__", "first")
rt_env_set("__SIMPLE_TEST_OVERWRITE__", "second")
val value = env_val("__SIMPLE_TEST_OVERWRITE__")
expect(value).to_equal("second")
rt_env_remove("__SIMPLE_TEST_OVERWRITE__")
```

</details>

### Build Environment

#### SHELL is set on unix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = env_val("SHELL")
val has_shell = shell != ""
expect(has_shell).to_equal(true)
```

</details>

#### LANG or LC variables exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = env_val("LANG")
val lc_all = env_val("LC_ALL")
val has_locale = lang != "" or lc_all != ""
expect(has_locale).to_equal(true)
```

</details>

#### TERM is set in interactive sessions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val term = env_val("TERM")
val has_term = term != ""
expect(has_term).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
