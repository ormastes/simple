# Claude Full Bash ParsedCommand

> Checks regex fallback and tree-sitter parsed command surfaces.

<!-- sdn-diagram:id=ParsedCommand_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ParsedCommand_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ParsedCommand_spec -> std
ParsedCommand_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ParsedCommand_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bash ParsedCommand

Checks regex fallback and tree-sitter parsed command surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/bash/ParsedCommand_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks regex fallback and tree-sitter parsed command surfaces.

## Scenarios

### Claude full ParsedCommand

#### should expose regex parsed command behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = RegexParsedCommand_DEPRECATED.new("echo one | grep o > out.txt")
expect(parsed.toString()).to_equal("echo one | grep o > out.txt")
expect(parsed.getPipeSegments()).to_equal(["echo one", "grep o > out.txt"])
expect(parsed.withoutOutputRedirections()).to_equal("echo one | grep o")
expect(parsed.getOutputRedirections()[0].target).to_equal("out.txt")
expect(parsed.getOutputRedirections()[0].operator).to_equal(">")
expect(parsed.getTreeSitterAnalysis().summary).to_equal("")
```

</details>

#### should expose tree-sitter parsed command behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val redir = OutputRedirection.new("log.txt", ">>")
val parsed = TreeSitterParsedCommand.new("printf ok | tee >> log.txt", [10], [redir], TreeSitterAnalysis.new(true, "safe"))
expect(parsed.toString()).to_equal("printf ok | tee >> log.txt")
expect(parsed.getPipeSegments()).to_equal(["printf ok", "tee >> log.txt"])
expect(parsed.withoutOutputRedirections()).to_equal("printf ok | tee")
expect(parsed.getOutputRedirections()[0].operator).to_equal(">>")
expect(parsed.getTreeSitterAnalysis().safe).to_equal(true)
```

</details>

#### should build parsed commands from precomputed root data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = buildParsedCommandFromRoot("echo ok", [], [], TreeSitterAnalysis.new(true, "ok"))
expect(built.getPipeSegments()).to_equal(["echo ok"])
expect(parseParsedCommand("echo fallback", false).toString()).to_equal("echo fallback")
expect(parsedCommandSourceLinesModeled()).to_equal(318)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
