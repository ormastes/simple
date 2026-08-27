# Test Lens (Editor Gutter Arrows) Specification

> Purpose: This spec proves Real test discovery for gutter arrows.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Lens (Editor Gutter Arrows) Specification

Purpose: This spec proves Real test discovery for gutter arrows.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1200-1205 (test lens / CodeLens) |
| Category | Editor / IDE Integration |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/integration/app/test_lens_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves Real test discovery for gutter arrows.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### Real test discovery for gutter arrows

#### math_render_spec.spl discovery

#### discovers all 129 test cases

- discovers all 129 test cases
   - Expected: code equals `0`
   - Expected: test_count equals `129`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTLENS-001
step("discovers all 129 test cases")
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

- discovers to_text rendering describe group
- discovers to_text rendering describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers to_text rendering describe group")
step("discovers to_text rendering describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_text rendering")
```

</details>

#### discovers to_debug rendering describe group

- discovers to_debug rendering describe group
- discovers to_debug rendering describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers to_debug rendering describe group")
step("discovers to_debug rendering describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_debug rendering")
```

</details>

#### discovers render_latex_raw rendering describe group

- discovers render_latex_raw rendering describe group
- discovers render_latex_raw rendering describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers render_latex_raw rendering describe group")
step("discovers render_latex_raw rendering describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("render_latex_raw rendering")
```

</details>

#### discovers to_pretty rendering describe group

- discovers to_pretty rendering describe group
- discovers to_pretty rendering describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers to_pretty rendering describe group")
step("discovers to_pretty rendering describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_pretty rendering")
```

</details>

#### discovers to_md rendering describe group

- discovers to_md rendering describe group
- discovers to_md rendering describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers to_md rendering describe group")
step("discovers to_md rendering describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("to_md rendering")
```

</details>

#### discovers rendering edge cases describe group

- discovers rendering edge cases describe group
- discovers rendering edge cases describe group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers rendering edge cases describe group")
step("discovers rendering edge cases describe group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("rendering edge cases")
```

</details>

#### discovers nested context > it hierarchy

- discovers nested context > it hierarchy
- discovers nested context > it hierarchy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers nested context > it hierarchy")
step("discovers nested context > it hierarchy")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
# Real discovery shows: describe > context > it
expect(stdout).to_contain("arithmetic > renders addition")
expect(stdout).to_contain("fractions > renders frac")
expect(stdout).to_contain("DL equations > renders sigmoid")
```

</details>

#### discovers deeply nested edge case tests

- discovers deeply nested edge case tests
- discovers deeply nested edge case tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers deeply nested edge case tests")
step("discovers deeply nested edge case tests")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
expect(stdout).to_contain("deeply nested > renders triple-nested frac")
expect(stdout).to_contain("complex DL architectures > renders GELU approximation")
```

</details>

#### loss_nograd_blocks_spec.spl discovery

#### discovers all 38 test cases

- discovers all 38 test cases
- discovers all 38 test cases
   - Expected: code equals `0`
   - Expected: test_count equals `38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers all 38 test cases")
step("discovers all 38 test cases")
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

- discovers loss{} block evaluation group
- discovers loss{} block evaluation group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers loss{} block evaluation group")
step("discovers loss{} block evaluation group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("loss{} block evaluation")
```

</details>

#### discovers nograd{} block evaluation group

- discovers nograd{} block evaluation group
- discovers nograd{} block evaluation group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers nograd{} block evaluation group")
step("discovers nograd{} block evaluation group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("nograd{} block evaluation")
```

</details>

#### discovers m{}/loss{}/nograd{} parity group

- discovers m{}/loss{}/nograd{} parity group
- discovers m{}/loss{}/nograd{} parity group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers m{}/loss{}/nograd{} parity group")
step("discovers m{}/loss{}/nograd{} parity group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("parity")
```

</details>

#### discovers DL equation tests in loss{} block

- discovers DL equation tests in loss{} block
- discovers DL equation tests in loss{} block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers DL equation tests in loss{} block")
step("discovers DL equation tests in loss{} block")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(stdout).to_contain("Sigmoid")
expect(stdout).to_contain("MSE component")
```

</details>

#### math_blocks_spec.spl discovery

#### discovers all 28 test cases

- discovers all 28 test cases
- discovers all 28 test cases
   - Expected: code equals `0`
   - Expected: test_count equals `28`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers all 28 test cases")
step("discovers all 28 test cases")
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

- discovers Math Block Arithmetic group
- discovers Math Block Arithmetic group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers Math Block Arithmetic group")
step("discovers Math Block Arithmetic group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("Math Block Arithmetic")
```

</details>

#### discovers Math Block Constants group

- discovers Math Block Constants group
- discovers Math Block Constants group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers Math Block Constants group")
step("discovers Math Block Constants group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("Math Block Constants")
```

</details>

#### discovers LaTeX Compatibility group

- discovers LaTeX Compatibility group
- discovers LaTeX Compatibility group


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("discovers LaTeX Compatibility group")
step("discovers LaTeX Compatibility group")
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_blocks_spec.spl"])
expect(stdout).to_contain("LaTeX Compatibility")
```

</details>

### Neovim test_lens.lua real detection

#### detects blocks via headless nvim

- detects blocks via headless nvim
- detects blocks via headless nvim


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects blocks via headless nvim")
step("detects blocks via headless nvim")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-TESTLENS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56cfb643967858272f28cc7fe491850c94ea8c73751a13d67409d66172ced41c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56cfb643967858272f28cc7fe491850c94ea8c73751a13d67409d66172ced41c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56cfb643967858272f28cc7fe491850c94ea8c73751a13d67409d66172ced41c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/test_lens_spec.spl
mirror: doc/06_spec/integration/app/test_lens_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/test_lens_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/test_lens_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/test_lens_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/test_lens_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers all 129 test cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/test_lens_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers to_text rendering describe group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/test_lens_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'discovers to_debug rendering describe group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
