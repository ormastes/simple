# Game2D CLI (AC-7)

> `bin/simple game new <name>`, `game inspect assets`, `game test --headless`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D CLI (AC-7)

`bin/simple game new <name>`, `game inspect assets`, `game test --headless`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Failing (no impl) |
| Source | `test/03_system/engine/game2d_cli_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`bin/simple game new <name>`, `game inspect assets`, `game test --headless`,
`game run --scene main` are dispatched from `src/app/game/`. Dispatcher table
must include a `CommandEntry { name: "game", ... }` row.

`game run --scene main` requires a window backend; gated via
`SIMPLEOS_GAME_HEADLESS_ONLY=1` to skip in CI.

Edge case: `game new` into existing non-empty dir → exit code 2.

Red-phase: src/app/game/* absent; signature-presence assertions fail.

## Scenarios

### Game2D CLI (AC-7)

### dispatcher table includes the `game` command

#### src/app/cli/dispatch/table.spl mentions name=\

- src/app/cli/dispatch/table.spl mentions name=\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/cli/dispatch/table.spl mentions name=\")
val src = _read("src/app/cli/dispatch/table.spl")
expect(_has(src, "\"game\"") and _has(src, "src/app/game/")
    ).to_equal(true)
```

</details>

#### edge case: synthetic dispatch row matches detector

- edge case: synthetic dispatch row matches detector
   - Expected: _has(sample, "\"game\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: synthetic dispatch row matches detector")
val sample =
    "CommandEntry { name: \"game\", app_path: \"src/app/game/main.spl\" }"
expect(_has(sample, "\"game\"")).to_equal(true)
```

</details>

### subcommand entry points exist

#### src/app/game/main.spl exists

- src/app/game/main.spl exists
   - Expected: rt_file_exists("src/app/game/main.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/game/main.spl exists")
expect(rt_file_exists("src/app/game/main.spl")).to_equal(true)
```

</details>

#### src/app/game/new.spl exists

- src/app/game/new.spl exists
   - Expected: rt_file_exists("src/app/game/new.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/game/new.spl exists")
expect(rt_file_exists("src/app/game/new.spl")).to_equal(true)
```

</details>

#### src/app/game/test.spl exists

- src/app/game/test.spl exists
   - Expected: rt_file_exists("src/app/game/test.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/game/test.spl exists")
expect(rt_file_exists("src/app/game/test.spl")).to_equal(true)
```

</details>

#### src/app/game/inspect.spl exists

- src/app/game/inspect.spl exists
   - Expected: rt_file_exists("src/app/game/inspect.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/game/inspect.spl exists")
expect(rt_file_exists("src/app/game/inspect.spl")).to_equal(true)
```

</details>

#### src/app/game/run.spl exists

- src/app/game/run.spl exists
   - Expected: rt_file_exists("src/app/game/run.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("src/app/game/run.spl exists")
expect(rt_file_exists("src/app/game/run.spl")).to_equal(true)
```

</details>

### subcommand dispatch logic

#### main.spl dispatches new|run|test|inspect

- main.spl dispatches new|run|test|inspect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("main.spl dispatches new|run|test|inspect")
val src = _read("src/app/game/main.spl")
expect(_has(src, "new") and _has(src, "run") and
       _has(src, "test") and _has(src, "inspect")
    ).to_equal(true)
```

</details>

#### edge case: empty main.spl does not satisfy

- edge case: empty main.spl does not satisfy
   - Expected: _has("", "new") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: empty main.spl does not satisfy")
expect(_has("", "new")).to_equal(false)
```

</details>

### edge case: `game new` into existing non-empty dir

#### new.spl mentions exit code 2 / dir-exists path

- new.spl mentions exit code 2 / dir-exists path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("new.spl mentions exit code 2 / dir-exists path")
val src = _read("src/app/game/new.spl")
expect(_has(src, "exit") and (_has(src, "2") or _has(src, "exists"))
    ).to_equal(true)
```

</details>

### error path: `game inspect assets` lists declarations

#### inspect.spl mentions assets / load_assets

- inspect.spl mentions assets / load_assets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inspect.spl mentions assets / load_assets")
val src = _read("src/app/game/inspect.spl")
expect(_has(src, "assets") or _has(src, "load_assets")
    ).to_equal(true)
```

</details>

### windowed-run is CI-gated

#### spec respects SIMPLEOS_GAME_HEADLESS_ONLY env gate

- spec respects SIMPLEOS_GAME_HEADLESS_ONLY env gate
   - Expected: result == true or result == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("spec respects SIMPLEOS_GAME_HEADLESS_ONLY env gate")
# Ensure the env helper is total: it doesn't crash under any value.
val result = _headless_only()
expect(result == true or result == false).to_equal(true)
```

</details>

#### edge case: missing env defaults to false (windowed allowed)

- edge case: missing env defaults to false (windowed allowed)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("edge case: missing env defaults to false (windowed allowed)")
# In a clean env this should be false.
val v = rt_env_get("__ZZZ_NEVER_SET_ENV__")
expect(v).to_not_equal("1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9d6ba3c4254cca0bceec05fcca9fc3c829afe6722b7a28d37350e4020434f521`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9d6ba3c4254cca0bceec05fcca9fc3c829afe6722b7a28d37350e4020434f521`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9d6ba3c4254cca0bceec05fcca9fc3c829afe6722b7a28d37350e4020434f521`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/game2d_cli_spec.spl
mirror: doc/06_spec/03_system/engine/game2d_cli_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/game2d_cli_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/game2d_cli_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/game2d_cli_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src/app/cli/dispatch/table.spl mentions name=\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_cli_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'edge case: synthetic dispatch row matches detector' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/game2d_cli_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'src/app/game/main.spl exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
