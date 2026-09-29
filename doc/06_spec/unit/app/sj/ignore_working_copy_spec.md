# Ignore Working Copy Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignore Working Copy Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/sj/ignore_working_copy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#
#
#
#

## Scenarios

### Ignore Working Copy - Read Verbs

#### injects --ignore-working-copy for jj log

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- injects --ignore-working-copy for jj log
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj log")
val result = inject_flags(["jj", "log"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj status

- injects --ignore-working-copy for jj status
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj status")
val result = inject_flags(["jj", "status"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj diff

- injects --ignore-working-copy for jj diff
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj diff")
val result = inject_flags(["jj", "diff"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj show

- injects --ignore-working-copy for jj show
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj show")
val result = inject_flags(["jj", "show"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj op log

- injects --ignore-working-copy for jj op log
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj op log")
val result = inject_flags(["jj", "op", "log"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj evolog

- injects --ignore-working-copy for jj evolog
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj evolog")
val result = inject_flags(["jj", "evolog"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file annotate

- injects --ignore-working-copy for jj file annotate
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj file annotate")
val result = inject_flags(["jj", "file", "annotate", "src/main.spl"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file list

- injects --ignore-working-copy for jj file list
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj file list")
val result = inject_flags(["jj", "file", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj file show

- injects --ignore-working-copy for jj file show
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj file show")
val result = inject_flags(["jj", "file", "show", "path"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj bookmark list

- injects --ignore-working-copy for jj bookmark list
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj bookmark list")
val result = inject_flags(["jj", "bookmark", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj config list

- injects --ignore-working-copy for jj config list
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj config list")
val result = inject_flags(["jj", "config", "list"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

#### injects --ignore-working-copy for jj op show

- injects --ignore-working-copy for jj op show
   - Expected: _has_flag(result, "--ignore-working-copy") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("injects --ignore-working-copy for jj op show")
val result = inject_flags(["jj", "op", "show"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(true)
```

</details>

### Ignore Working Copy - No-Pager and Color

#### all commands get --no-pager

- all commands get --no-pager
   - Expected: _has_flag(result, "--no-pager") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all commands get --no-pager")
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--no-pager")).to_equal(true)
```

</details>

#### all commands get --color never

- all commands get --color never
   - Expected: _has_flag(result, "--color") is true
   - Expected: _has_flag(result, "never") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all commands get --color never")
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--color")).to_equal(true)
expect(_has_flag(result, "never")).to_equal(true)
```

</details>

### Ignore Working Copy - Negative Cases

#### does NOT inject --ignore-working-copy for jj describe

- does NOT inject --ignore-working-copy for jj describe
   - Expected: _has_flag(result, "--ignore-working-copy") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT inject --ignore-working-copy for jj describe")
val result = inject_flags(["jj", "describe", "-m", "test"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does NOT inject --ignore-working-copy for jj new

- does NOT inject --ignore-working-copy for jj new
   - Expected: _has_flag(result, "--ignore-working-copy") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT inject --ignore-working-copy for jj new")
val result = inject_flags(["jj", "new"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does NOT inject --ignore-working-copy for jj rebase

- does NOT inject --ignore-working-copy for jj rebase
   - Expected: _has_flag(result, "--ignore-working-copy") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT inject --ignore-working-copy for jj rebase")
val result = inject_flags(["jj", "rebase", "-d", "main"])
expect(_has_flag(result, "--ignore-working-copy")).to_equal(false)
```

</details>

#### does not modify non-jj commands

- does not modify non-jj commands
   - Expected: result.len() equals `2i64`
   - Expected: result[0i64] equals `git`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not modify non-jj commands")
val result = inject_flags(["git", "status"])
expect(result.len()).to_equal(2i64)
expect(result[0i64]).to_equal("git")
```

</details>

#### build_command combines inject and join

- build_command combines inject and join


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build_command combines inject and join")
val cmd = build_command(["jj", "log"])
expect(cmd).to_contain("--ignore-working-copy")
expect(cmd).to_contain("--no-pager")
```

</details>

### Ignore Working Copy - is_read_bypass contract

#### recognises the bare read verbs

- recognises the bare read verbs
   - Expected: is_read_bypass(["jj", "log"]) is true
   - Expected: is_read_bypass(["jj", "status"]) is true
   - Expected: is_read_bypass(["jj", "diff"]) is true
   - Expected: is_read_bypass(["jj", "show"]) is true
   - Expected: is_read_bypass(["jj", "evolog"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises the bare read verbs")
expect(is_read_bypass(["jj", "log"])).to_equal(true)
expect(is_read_bypass(["jj", "status"])).to_equal(true)
expect(is_read_bypass(["jj", "diff"])).to_equal(true)
expect(is_read_bypass(["jj", "show"])).to_equal(true)
expect(is_read_bypass(["jj", "evolog"])).to_equal(true)
```

</details>

#### recognises the two-word read verbs

- recognises the two-word read verbs
   - Expected: is_read_bypass(["jj", "op", "log"]) is true
   - Expected: is_read_bypass(["jj", "op", "show"]) is true
   - Expected: is_read_bypass(["jj", "file", "annotate"]) is true
   - Expected: is_read_bypass(["jj", "file", "list"]) is true
   - Expected: is_read_bypass(["jj", "file", "show"]) is true
   - Expected: is_read_bypass(["jj", "bookmark", "list"]) is true
   - Expected: is_read_bypass(["jj", "config", "list"]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognises the two-word read verbs")
expect(is_read_bypass(["jj", "op", "log"])).to_equal(true)
expect(is_read_bypass(["jj", "op", "show"])).to_equal(true)
expect(is_read_bypass(["jj", "file", "annotate"])).to_equal(true)
expect(is_read_bypass(["jj", "file", "list"])).to_equal(true)
expect(is_read_bypass(["jj", "file", "show"])).to_equal(true)
expect(is_read_bypass(["jj", "bookmark", "list"])).to_equal(true)
expect(is_read_bypass(["jj", "config", "list"])).to_equal(true)
```

</details>

#### rejects mutating subcommands of the two-word families

- rejects mutating subcommands of the two-word families
   - Expected: is_read_bypass(["jj", "op", "restore", "abc"]) is false
   - Expected: is_read_bypass(["jj", "bookmark", "set", "main"]) is false
   - Expected: is_read_bypass(["jj", "config", "set", "k", "v"]) is false
   - Expected: is_read_bypass(["jj", "file", "track", "x"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects mutating subcommands of the two-word families")
expect(is_read_bypass(["jj", "op", "restore", "abc"])).to_equal(false)
expect(is_read_bypass(["jj", "bookmark", "set", "main"])).to_equal(false)
expect(is_read_bypass(["jj", "config", "set", "k", "v"])).to_equal(false)
expect(is_read_bypass(["jj", "file", "track", "x"])).to_equal(false)
```

</details>

#### rejects an empty or verbless argv

- rejects an empty or verbless argv
   - Expected: is_read_bypass([]) is false
   - Expected: is_read_bypass(["jj"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty or verbless argv")
expect(is_read_bypass([])).to_equal(false)
expect(is_read_bypass(["jj"])).to_equal(false)
```

</details>

#### a bare two-word family head is not a read verb

- a bare two-word family head is not a read verb
   - Expected: is_read_bypass(["jj", "op"]) is false
   - Expected: is_read_bypass(["jj", "bookmark"]) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bare two-word family head is not a read verb")
# `jj op` with no subcommand takes the argv.len() > 1 branch, giving
# key == "op", which is in none of the read-verb cases.
expect(is_read_bypass(["jj", "op"])).to_equal(false)
expect(is_read_bypass(["jj", "bookmark"])).to_equal(false)
```

</details>

### Ignore Working Copy - emitted argv shape

#### emits jj, the bypass flag, then the pager and colour flags, then the verb

- emits jj, the bypass flag, then the pager and colour flags, then the verb
   - Expected: result[0i64] equals `jj`
   - Expected: result[1i64] equals `--ignore-working-copy`
   - Expected: result[2i64] equals `--no-pager`
   - Expected: result[3i64] equals `--color`
   - Expected: result[4i64] equals `never`
   - Expected: result[5i64] equals `log`
   - Expected: result[6i64] equals `-r`
   - Expected: result[7i64] equals `@`
   - Expected: result.len() equals `8i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits jj, the bypass flag, then the pager and colour flags, then the verb")
val result = inject_flags(["jj", "log", "-r", "@"])
expect(result[0i64]).to_equal("jj")
expect(result[1i64]).to_equal("--ignore-working-copy")
expect(result[2i64]).to_equal("--no-pager")
expect(result[3i64]).to_equal("--color")
expect(result[4i64]).to_equal("never")
expect(result[5i64]).to_equal("log")
expect(result[6i64]).to_equal("-r")
expect(result[7i64]).to_equal("@")
expect(result.len()).to_equal(8i64)
```

</details>

#### omits only the bypass flag for a write verb

- omits only the bypass flag for a write verb
   - Expected: result[0i64] equals `jj`
   - Expected: result[1i64] equals `--no-pager`
   - Expected: result[2i64] equals `--color`
   - Expected: result[3i64] equals `never`
   - Expected: result[4i64] equals `new`
   - Expected: result.len() equals `5i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits only the bypass flag for a write verb")
val result = inject_flags(["jj", "new"])
expect(result[0i64]).to_equal("jj")
expect(result[1i64]).to_equal("--no-pager")
expect(result[2i64]).to_equal("--color")
expect(result[3i64]).to_equal("never")
expect(result[4i64]).to_equal("new")
expect(result.len()).to_equal(5i64)
```

</details>

#### returns a non-jj argv completely untouched

- returns a non-jj argv completely untouched
   - Expected: result.len() equals `3i64`
   - Expected: result[2i64] equals `--force`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a non-jj argv completely untouched")
val result = inject_flags(["git", "push", "--force"])
expect(result.len()).to_equal(3i64)
expect(result[2i64]).to_equal("--force")
```

</details>

#### returns an empty argv untouched

- returns an empty argv untouched
   - Expected: inject_flags([]).len() equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty argv untouched")
expect(inject_flags([]).len()).to_equal(0i64)
```

</details>

#### build_command renders the whole line space-separated

- build_command renders the whole line space-separated
   - Expected: build_command(["jj", "log"]) equals `jj --ignore-working-copy --no-pager --color never log`
   - Expected: build_command(["jj", "new"]) equals `jj --no-pager --color never new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("build_command renders the whole line space-separated")
expect(build_command(["jj", "log"])).to_equal("jj --ignore-working-copy --no-pager --color never log")
expect(build_command(["jj", "new"])).to_equal("jj --no-pager --color never new")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `260f8873deff742815a0d3cf8fcc0350b6178b4d0cd259ca94044497d4f28ab5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `260f8873deff742815a0d3cf8fcc0350b6178b4d0cd259ca94044497d4f28ab5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `260f8873deff742815a0d3cf8fcc0350b6178b4d0cd259ca94044497d4f28ab5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sj/ignore_working_copy_spec.spl
mirror: doc/06_spec/unit/app/sj/ignore_working_copy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sj/ignore_working_copy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sj/ignore_working_copy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sj/ignore_working_copy_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects --ignore-working-copy for jj log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/ignore_working_copy_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects --ignore-working-copy for jj status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sj/ignore_working_copy_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects --ignore-working-copy for jj diff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
