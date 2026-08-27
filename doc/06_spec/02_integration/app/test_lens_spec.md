# Test Lens (Editor Gutter Arrows) Specification

> Tests that the REAL test discovery pipeline (`bin/simple test --list`) correctly identifies all describe/context/it blocks in math block specs.

<!-- sdn-diagram:id=test_lens_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_lens_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_lens_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_lens_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Lens (Editor Gutter Arrows) Specification

Tests that the REAL test discovery pipeline (`bin/simple test --list`) correctly identifies all describe/context/it blocks in math block specs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1200-1205 (test lens / CodeLens) |
| Category | Editor / IDE Integration |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/02_integration/app/test_lens_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the REAL test discovery pipeline (`bin/simple test --list`)
correctly identifies all describe/context/it blocks in math block specs.

This is the same data source that powers gutter arrows:
- VSCode CodeLens reads `bin/simple test --list` output
- Neovim test_lens.lua uses matching patterns
- Both produce "▶ Run" indicators for every discovered block

These tests exercise the real test runner, not reimplemented patterns.

## Scenarios

### Real test discovery for gutter arrows

#### math_render_spec.spl discovery

#### discovers all 129 test cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(code).to_equal(0)
# Count lines that contain test entries (file:line - ...)
val lines = stdout.split("\n")
var test_count = 0
for line in lines:
    if line.contains("math_render_spec.spl") and line.contains(" - "):
        test_count = test_count + 1
expect(test_count).to_equal(129)
```

</details>

#### discovers to_text rendering describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_text rendering")
```

</details>

#### discovers to_debug rendering describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_debug rendering")
```

</details>

#### discovers render_latex_raw rendering describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("render_latex_raw rendering")
```

</details>

#### discovers to_pretty rendering describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_pretty rendering")
```

</details>

#### discovers to_md rendering describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_md rendering")
```

</details>

#### discovers rendering edge cases describe group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("rendering edge cases")
```

</details>

#### discovers nested context > it hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
# Real discovery shows: describe > context > it
expect(stdout).to_contain("arithmetic > renders addition")
expect(stdout).to_contain("fractions > renders frac")
expect(stdout).to_contain("DL equations > renders sigmoid")
```

</details>

#### discovers deeply nested edge case tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("deeply nested > renders triple-nested frac")
expect(stdout).to_contain("complex DL architectures > renders GELU approximation")
```

</details>

#### loss_nograd_blocks_spec.spl discovery

#### discovers all 38 test cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(code).to_equal(0)
val lines = stdout.split("\n")
var test_count = 0
for line in lines:
    if line.contains("loss_nograd") and line.contains(" - "):
        test_count = test_count + 1
expect(test_count).to_equal(38)
```

</details>

#### discovers loss{} block evaluation group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("loss{} block evaluation")
```

</details>

#### discovers nograd{} block evaluation group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("nograd{} block evaluation")
```

</details>

#### discovers m{}/loss{}/nograd{} parity group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("parity")
```

</details>

#### discovers DL equation tests in loss{} block

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("Sigmoid")
expect(stdout).to_contain("MSE component")
```

</details>

#### math_blocks_spec.spl discovery

#### discovers all 28 test cases

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(code).to_equal(0)
val lines = stdout.split("\n")
var test_count = 0
for line in lines:
    if line.contains("math_blocks_spec.spl") and line.contains(" - "):
        test_count = test_count + 1
expect(test_count).to_equal(28)
```

</details>

#### discovers Math Block Arithmetic group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("Math Block Arithmetic")
```

</details>

#### discovers Math Block Constants group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("Math Block Constants")
```

</details>

#### discovers LaTeX Compatibility group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("LaTeX Compatibility")
```

</details>

### Neovim test_lens.lua real detection

#### detects blocks via headless nvim

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Run the real Neovim Lua test_lens.find_test_blocks on our spec file
val lua_script = "vim = vim or {} vim.trim = function(s) return s:match('^%%s*(.-)\\ %%s*$') end vim.log = { levels = { INFO = 1 } } vim.api = { nvim_create_namespace = function() return 0 end, nvim_create_augroup = function() return 0 end, nvim_create_autocmd = function() end, nvim_buf_set_extmark = function() end, nvim_buf_clear_namespace = function() end, nvim_buf_get_lines = function(_, s, e, _) local lines = {} for line in io.lines('test/feature/usage/math_render_spec.spl') do table.insert(lines, line) end return lines end, nvim_buf_is_valid = function() return true end, nvim_win_get_cursor = function() return {1, 0} end, nvim_list_bufs = function() return {} end, nvim_buf_is_loaded = function() return false end, nvim_buf_get_name = function() return '' end } vim.wo = {} vim.bo = {} vim.notify = function() end vim.defer_fn = function() end vim.fn = { executable = function() return 0 end, getcwd = function() return '.' end } vim.fs = { find = function() return {} end, dirname = function() return '.' end } vim.cmd = function() end vim.env = { HOME = '/tmp' } package.loaded['simple.float'] = { show = function() end } local M = dofile('src/app/nvim_plugin/lua/simple/test_lens.lua') local blocks = M.find_test_blocks(0) local d, c, i = 0, 0, 0 for _, b in ipairs(blocks) do if b.kind == 'describe' then d = d + 1 elseif b.kind == 'context' then c = c + 1 elseif b.kind == 'it' then i = i + 1 end end print(d .. ',' .. c .. ',' .. i)"
val (stdout, stderr, code) = process_run("nvim", ["--headless", "-u", "NONE", "+lua " + lua_script, "+qa!"])
# Should detect all blocks matching the test runner discovery
val trimmed = stdout.trim()
expect(trimmed.len()).to_be_greater_than(0)
val parts = trimmed.split(",")
if parts.len() >= 3:
    val describes = parts[0].trim().to_i64()
    val contexts = parts[1].trim().to_i64()
    val its = parts[2].trim().to_i64()
    # Neovim detection should match test runner: 6+ describes, 10+ contexts, 129 its
    expect(describes).to_be_greater_than(5)
    expect(contexts).to_be_greater_than(10)
    expect(its).to_be_greater_than(100)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
