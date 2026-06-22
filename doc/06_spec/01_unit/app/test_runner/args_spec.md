# Args Specification

> <details>

<!-- sdn-diagram:id=args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

args_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Args Specification

## Scenarios

### parse_mode_str

#### parses native mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("native")
expect(mode == TestExecutionMode.Native).to_equal(true)
```

</details>

#### parses binary as native mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("binary")
expect(mode == TestExecutionMode.Native).to_equal(true)
```

</details>

#### parses smf mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("smf")
expect(mode == TestExecutionMode.Smf).to_equal(true)
```

</details>

#### parses loader as smf mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("loader")
expect(mode == TestExecutionMode.Smf).to_equal(true)
```

</details>

#### defaults to Interpreter for unknown string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("unknown")
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

#### defaults to Interpreter for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("")
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

#### defaults to Interpreter for interpreter string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("interpreter")
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

#### is case-sensitive (NATIVE does not match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("NATIVE")
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

#### is case-sensitive (Smf does not match)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode = parse_mode_str("Smf")
expect(mode == TestExecutionMode.Interpreter).to_equal(true)
```

</details>

### parse_test_args

### default values

#### uses test/ as default path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["path"]).to_equal("test/")
```

</details>

#### defaults level to all

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["level"]).to_equal("all")
```

</details>

#### defaults tag to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["tag"]).to_equal("")
```

</details>

#### defaults fail_fast to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["fail_fast"]).to_equal(false)
```

</details>

#### defaults mode to interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["mode"]).to_equal("interpreter")
```

</details>

#### defaults timeout to 120

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["timeout"]).to_equal(120)
```

</details>

#### defaults list to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["list"]).to_equal(false)
```

</details>

#### defaults verbose to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["verbose"]).to_equal(false)
```

</details>

#### defaults coverage to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["coverage"]).to_equal(false)
```

</details>

#### defaults no_db to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args([])
expect(opts["no_db"]).to_equal(false)
```

</details>

### path argument

#### accepts positional path argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["test/unit/"])
expect(opts["path"]).to_equal("test/unit/")
```

</details>

#### accepts file path as argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["test/my_spec.spl"])
expect(opts["path"]).to_equal("test/my_spec.spl")
```

</details>

#### ignores second positional argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["first/path", "second/path"])
expect(opts["path"]).to_equal("first/path")
```

</details>

### level flags

#### parses --unit flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--unit"])
expect(opts["level"]).to_equal("unit")
```

</details>

#### parses --integration flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--integration"])
expect(opts["level"]).to_equal("integration")
```

</details>

#### parses --system flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--system"])
expect(opts["level"]).to_equal("system")
```

</details>

### boolean flags

#### parses --fail-fast

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--fail-fast"])
expect(opts["fail_fast"]).to_equal(true)
```

</details>

#### parses --list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--list"])
expect(opts["list"]).to_equal(true)
```

</details>

#### parses --list-ignored sets both list and list_ignored

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--list-ignored"])
expect(opts["list"]).to_equal(true)
expect(opts["list_ignored"]).to_equal(true)
```

</details>

#### parses --only-slow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--only-slow"])
expect(opts["only_slow"]).to_equal(true)
```

</details>

#### parses --only-skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--only-skipped"])
expect(opts["only_skipped"]).to_equal(true)
```

</details>

#### parses --show-tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--show-tags"])
expect(opts["show_tags"]).to_equal(true)
```

</details>

#### parses --gc-log

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--gc-log"])
expect(opts["gc_log"]).to_equal(true)
```

</details>

#### parses --gc=off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--gc=off"])
expect(opts["gc_off"]).to_equal(true)
```

</details>

#### parses --gc=OFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--gc=OFF"])
expect(opts["gc_off"]).to_equal(true)
```

</details>

#### parses --safe-mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--safe-mode"])
expect(opts["safe_mode"]).to_equal(true)
```

</details>

#### parses --safe as alias for safe-mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--safe"])
expect(opts["safe_mode"]).to_equal(true)
```

</details>

#### parses --force-rebuild

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--force-rebuild"])
expect(opts["force_rebuild"]).to_equal(true)
```

</details>

#### parses --keep-artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--keep-artifacts"])
expect(opts["keep_artifacts"]).to_equal(true)
```

</details>

#### parses --capture-screenshots

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--capture-screenshots"])
expect(opts["capture_screenshots"]).to_equal(true)
```

</details>

#### parses --screenshots as the public alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--screenshots"])
expect(opts["capture_screenshots"]).to_equal(true)
```

</details>

#### parses --refresh-screenshots

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--refresh-screenshots"])
expect(opts["refresh_gui_images"]).to_equal(true)
expect(opts["capture_screenshots"]).to_equal(true)
```

</details>

#### keeps --refresh-gui-image as a compatibility alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--refresh-gui-image"])
expect(opts["refresh_gui_images"]).to_equal(true)
expect(opts["capture_screenshots"]).to_equal(true)
```

</details>

#### parses --screenshot-output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--screenshot-output", "doc/06_spec/image"])
expect(opts["capture_screenshots"]).to_equal(true)
expect(opts["screenshot_output"]).to_equal("doc/06_spec/image")
```

</details>

#### preserves a custom screenshot output root

<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--screenshots", "--screenshot-output", "doc/06_spec/image/custom"])
expect(opts["capture_screenshots"]).to_equal(true)
expect(opts["screenshot_output"]).to_equal("doc/06_spec/image/custom")

it "parses --all":
    val opts = parse_test_args(["--all"])
    expect(opts["run_all"]).to_equal(true)

it "parses --no-limits":
    val opts = parse_test_args(["--no-limits"])
    expect(opts["no_limits"]).to_equal(true)

it "parses --no-db":
    val opts = parse_test_args(["--no-db"])
    expect(opts["no_db"]).to_equal(true)

it "parses --verbose":
    val opts = parse_test_args(["--verbose"])
    expect(opts["verbose"]).to_equal(true)

it "parses -v as alias for verbose":
    val opts = parse_test_args(["-v"])
    expect(opts["verbose"]).to_equal(true)

it "parses --quick sets no_db":
    val opts = parse_test_args(["--quick"])
    expect(opts["no_db"]).to_equal(true)

it "parses -q as alias for quick":
    val opts = parse_test_args(["-q"])
    expect(opts["no_db"]).to_equal(true)

it "parses --coverage":
    val opts = parse_test_args(["--coverage"])
    expect(opts["coverage"]).to_equal(true)
```

</details>

### sdoctest flags

#### parses --sdoctest

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--sdoctest"])
expect(opts["sdoctest"]).to_equal(true)
```

</details>

#### parses --sdoctest-force

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--sdoctest-force"])
expect(opts["sdoctest_force"]).to_equal(true)
```

</details>

#### parses --sdoctest-env= with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--sdoctest-env=production"])
expect(opts["sdoctest_env"]).to_equal("production")
```

</details>

#### parses --sdoctest-env with next arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--sdoctest-env", "staging"])
expect(opts["sdoctest_env"]).to_equal("staging")
```

</details>

### skip features flags

#### parses --list-skip-features sets list, only_skipped, and list_skip_features

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--list-skip-features"])
expect(opts["list_skip_features"]).to_equal(true)
expect(opts["only_skipped"]).to_equal(true)
expect(opts["list"]).to_equal(true)
```

</details>

#### parses --skip-features as alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--skip-features"])
expect(opts["list_skip_features"]).to_equal(true)
expect(opts["only_skipped"]).to_equal(true)
expect(opts["list"]).to_equal(true)
```

</details>

### planned/pending flags

#### parses --planned-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--planned-only"])
expect(opts["planned_only"]).to_equal(true)
```

</details>

#### parses --pending as alias for planned-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--pending"])
expect(opts["planned_only"]).to_equal(true)
```

</details>

### value arguments

#### parses --tag with next arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--tag", "integration"])
expect(opts["tag"]).to_equal("integration")
```

</details>

#### parses --doc format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--doc"])
expect(opts["format"]).to_equal("doc")
```

</details>

#### parses --format doc

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--format", "doc"])
expect(opts["format"]).to_equal("doc")
```

</details>

#### parses --mode with next arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--mode", "native"])
expect(opts["mode"]).to_equal("native")
```

</details>

#### parses --mode= with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--mode=smf"])
expect(opts["mode"]).to_equal("smf")
```

</details>

#### parses --timeout with next arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--timeout", "300"])
expect(opts["timeout"]).to_equal(300)
```

</details>

#### parses --seed with next arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--seed", "42"])
expect(opts["seed"]).to_equal(42)
expect(opts["has_seed"]).to_equal(true)
```

</details>

### combined arguments

#### parses path with flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["test/unit/", "--fail-fast", "--verbose"])
expect(opts["path"]).to_equal("test/unit/")
expect(opts["fail_fast"]).to_equal(true)
expect(opts["verbose"]).to_equal(true)
```

</details>

#### parses flags before path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--fail-fast", "test/my_spec.spl"])
expect(opts["path"]).to_equal("test/my_spec.spl")
expect(opts["fail_fast"]).to_equal(true)
```

</details>

#### parses multiple flags together

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--unit", "--fail-fast", "--gc-log", "--verbose", "--coverage"])
expect(opts["level"]).to_equal("unit")
expect(opts["fail_fast"]).to_equal(true)
expect(opts["gc_log"]).to_equal(true)
expect(opts["verbose"]).to_equal(true)
expect(opts["coverage"]).to_equal(true)
```

</details>

#### parses sdoctest with env and force

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opts = parse_test_args(["--sdoctest", "--sdoctest-env=test", "--sdoctest-force"])
expect(opts["sdoctest"]).to_equal(true)
expect(opts["sdoctest_env"]).to_equal("test")
expect(opts["sdoctest_force"]).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_mode_str
- parse_test_args
- default values
- path argument
- level flags
- boolean flags
- sdoctest flags
- skip features flags
- planned/pending flags
- value arguments
- combined arguments

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
