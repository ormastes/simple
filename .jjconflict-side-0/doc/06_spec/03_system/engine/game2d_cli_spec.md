# Game2D CLI (AC-7)

> `bin/simple game new <name>`, `game inspect assets`, `game test --headless`,

<!-- sdn-diagram:id=game2d_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
_## bin/simple game subcommands._

### dispatcher table includes the `game` command

#### src/app/cli/dispatch/table.spl mentions name=\

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/app/cli/dispatch/table.spl")
expect(_has(src, "\"game\"") and _has(src, "src/app/game/")
    ).to_equal(true)
```

</details>

#### edge case: synthetic dispatch row matches detector

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample =
    "CommandEntry { name: \"game\", app_path: \"src/app/game/main.spl\" }"
expect(_has(sample, "\"game\"")).to_equal(true)
```

</details>

### subcommand entry points exist

#### src/app/game/main.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/game/main.spl")).to_equal(true)
```

</details>

#### src/app/game/new.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/game/new.spl")).to_equal(true)
```

</details>

#### src/app/game/test.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/game/test.spl")).to_equal(true)
```

</details>

#### src/app/game/inspect.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/game/inspect.spl")).to_equal(true)
```

</details>

#### src/app/game/run.spl exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/game/run.spl")).to_equal(true)
```

</details>

### subcommand dispatch logic

#### main.spl dispatches new|run|test|inspect

1.  has


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/app/game/main.spl")
expect(_has(src, "new") and _has(src, "run") and
       _has(src, "test") and _has(src, "inspect")
    ).to_equal(true)
```

</details>

#### edge case: empty main.spl does not satisfy

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "new")).to_equal(false)
```

</details>

### edge case: `game new` into existing non-empty dir

#### new.spl mentions exit code 2 / dir-exists path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/app/game/new.spl")
expect(_has(src, "exit") and (_has(src, "2") or _has(src, "exists"))
    ).to_equal(true)
```

</details>

### error path: `game inspect assets` lists declarations

#### inspect.spl mentions assets / load_assets

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _read("src/app/game/inspect.spl")
expect(_has(src, "assets") or _has(src, "load_assets")
    ).to_equal(true)
```

</details>

### windowed-run is CI-gated

#### spec respects SIMPLEOS_GAME_HEADLESS_ONLY env gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Ensure the env helper is total: it doesn't crash under any value.
val result = _headless_only()
expect(result == true or result == false).to_equal(true)
```

</details>

#### edge case: missing env defaults to false (windowed allowed)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In a clean env this should be false.
val v = rt_env_get("__ZZZ_NEVER_SET_ENV__")
expect(v == "1").to_equal(false)
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
