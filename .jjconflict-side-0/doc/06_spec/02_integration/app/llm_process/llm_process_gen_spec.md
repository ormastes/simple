# Llm Process Gen Specification

> <details>

<!-- sdn-diagram:id=llm_process_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_process_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_process_gen_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_process_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Process Gen Specification

## Scenarios

### llm-process-gen

#### is registered in the command tables

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell("rg -n 'name: \"llm-process-gen\"' src/compiler_rust/driver/src/main.rs").exit_code).to_equal(0)
expect(shell("rg -n 'name: \"llm-process-gen\"' src/app/cli/dispatch/table.spl").exit_code).to_equal(0)
```

</details>

#### reports a missing manifest as check failure

1. shell
   - Expected: result.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("missing")
shell("rm -rf '" + r + "' && mkdir -p '" + r + "'")
val result = run_gen(["check", "--root", r])
expect(result.exit_code).to_equal(1)
expect(result.stdout).to_contain("missing manifest")
```

</details>

#### creates a missing managed target and then check passes

1. seed
   - Expected: run_gen(["check", "--root", r]).exit_code equals `1`
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`
   - Expected: rt_file_exists(r + "/out/generated.md") is true
   - Expected: run_gen(["check", "--root", r]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("create")
seed(r, "managed")
expect(run_gen(["check", "--root", r]).exit_code).to_equal(1)
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
expect(rt_file_exists(r + "/out/generated.md")).to_equal(true)
expect(run_gen(["check", "--root", r]).exit_code).to_equal(0)
```

</details>

#### refuses manual edits unless force is supplied

1. seed
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`
   - Expected: shell("printf '\\nmanual edit\\n' >> '" + r + "/out/generated.md'").exit_code equals `0`
   - Expected: refused.exit_code equals `1`
   - Expected: run_gen(["generate", "--force", "--root", r]).exit_code equals `0`
   - Expected: regenerated does not contain `manual edit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("manual")
seed(r, "managed")
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
expect(shell("printf '\\nmanual edit\\n' >> '" + r + "/out/generated.md'").exit_code).to_equal(0)
val refused = run_gen(["generate", "--root", r])
expect(refused.exit_code).to_equal(1)
expect(refused.stdout).to_contain("refusing")
expect(run_gen(["generate", "--force", "--root", r]).exit_code).to_equal(0)
val regenerated = read_file(r + "/out/generated.md")
expect(regenerated.contains("manual edit")).to_equal(false)
```

</details>

#### renders Gemini TOML command files as managed skills

1. seed
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("gemini")
seed(r, "gemini_toml_skill")
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
val content = read_file(r + "/out/generated.md")
expect(content).to_contain("llm-process-gen: managed")
expect(content).to_contain("Demo command")
expect(content).to_contain("Run demo.")
```

</details>

#### generates managed tools metadata

1. seed tools
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("tools")
seed_tools(r)
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
val content = read_file(r + "/doc/00_llm_process/skill_command/skills/codex/demo/tools.sdn")
expect(content).to_contain("llm-process-gen: managed")
expect(content).to_contain("skill_tools |skill, source|")
expect(content).to_contain("simple_mcp")
```

</details>

#### generates Claude lib tools metadata

1. seed claude lib tools
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("claude_lib_tools")
seed_claude_lib_tools(r)
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
val content = read_file(r + "/doc/00_llm_process/skill_command/skills/claude/lib/demo/tools.sdn")
expect(content).to_contain("llm-process-gen: managed")
expect(content).to_contain("demo, claude_lib")
expect(content).to_contain("Run project-specific query")
```

</details>

#### lists managed records as json

1. seed
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("list")
seed(r, "managed")
val result = run_gen(["list", "--root", r, "--json"])
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("\"records\":1")
expect(result.stdout).to_contain("\"id\":\"sample_doc\"")
expect(result.stdout).to_contain("\"mode\":\"managed\"")
```

</details>

#### filters listed records by owner mode and stage

1. seed list filters
   - Expected: by_owner.exit_code equals `0`
   - Expected: owner_has_gemini is false
   - Expected: by_mode.exit_code equals `0`
   - Expected: mode_has_codex_a is false
   - Expected: by_stage.exit_code equals `0`
   - Expected: stage_has_codex_a is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("list_filters")
seed_list_filters(r)
val by_owner = run_gen(["list", "--root", r, "--json", "--owner", "codex"])
expect(by_owner.exit_code).to_equal(0)
expect(by_owner.stdout).to_contain("\"records\":2")
expect(by_owner.stdout).to_contain("\"id\":\"codex_a\"")
expect(by_owner.stdout).to_contain("\"id\":\"codex_tools\"")
val owner_has_gemini = by_owner.stdout.contains("\"id\":\"gemini_b\"")
expect(owner_has_gemini).to_equal(false)
val by_mode = run_gen(["list", "--root", r, "--json", "--mode=tools_sdn"])
expect(by_mode.exit_code).to_equal(0)
expect(by_mode.stdout).to_contain("\"records\":1")
expect(by_mode.stdout).to_contain("\"id\":\"codex_tools\"")
val mode_has_codex_a = by_mode.stdout.contains("\"id\":\"codex_a\"")
expect(mode_has_codex_a).to_equal(false)
val by_stage = run_gen(["list", "--root", r, "--stage", "design"])
expect(by_stage.exit_code).to_equal(0)
expect(by_stage.stdout).to_contain("gemini_b")
val stage_has_codex_a = by_stage.stdout.contains("codex_a")
expect(stage_has_codex_a).to_equal(false)
```

</details>

#### rejects unsupported generated file modes

1. seed invalid mode
   - Expected: checked.exit_code equals `1`
   - Expected: generated.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("invalid_mode")
seed_invalid_mode(r)
val checked = run_gen(["check", "--root", r])
expect(checked.exit_code).to_equal(1)
expect(checked.stdout).to_contain("unsupported mode tool_sdn")
val generated = run_gen(["generate", "--root", r])
expect(generated.exit_code).to_equal(1)
expect(generated.stdout).to_contain("unsupported mode tool_sdn")
```

</details>

#### renders pipe stage tools with stage-specific tool sets

1. seed pipe tools
   - Expected: run_gen(["generate", "--root", research_root]).exit_code equals `0`
   - Expected: research_has_duplicate_check is false
2. seed pipe tools
   - Expected: run_gen(["generate", "--root", design_root]).exit_code equals `0`
3. seed pipe tools
   - Expected: run_gen(["generate", "--root", release_root]).exit_code equals `0`
4. seed pipe tools
   - Expected: run_gen(["generate", "--root", verify_root]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val research_root = root("pipe_research")
seed_pipe_tools(research_root, "pipe_research_tools", "research", "doc/00_llm_process/skill_command/skills/pipe/research/tools.sdn")
expect(run_gen(["generate", "--root", research_root]).exit_code).to_equal(0)
val research = read_file(research_root + "/doc/00_llm_process/skill_command/skills/pipe/research/tools.sdn")
expect(research).to_contain("simple_mcp")
expect(research).to_contain("playwright")
val research_has_duplicate_check = research.contains("duplicate_check")
expect(research_has_duplicate_check).to_equal(false)

val design_root = root("pipe_design")
seed_pipe_tools(design_root, "pipe_design_tools", "design", "doc/00_llm_process/skill_command/skills/pipe/design/tools.sdn")
expect(run_gen(["generate", "--root", design_root]).exit_code).to_equal(0)
val design = read_file(design_root + "/doc/00_llm_process/skill_command/skills/pipe/design/tools.sdn")
expect(design).to_contain("simple_lsp_mcp")
expect(design).to_contain("spipe")

val release_root = root("pipe_release")
seed_pipe_tools(release_root, "pipe_release_tools", "release", "doc/00_llm_process/skill_command/skills/pipe/release/tools.sdn")
expect(run_gen(["generate", "--root", release_root]).exit_code).to_equal(0)
val release = read_file(release_root + "/doc/00_llm_process/skill_command/skills/pipe/release/tools.sdn")
expect(release).to_contain("version_files")
expect(release).to_contain("npm")

val verify_root = root("pipe_verify")
seed_pipe_tools(verify_root, "pipe_verify_tools", "verify", "doc/00_llm_process/skill_command/skills/pipe/verify/tools.sdn")
expect(run_gen(["generate", "--root", verify_root]).exit_code).to_equal(0)
val verify = read_file(verify_root + "/doc/00_llm_process/skill_command/skills/pipe/verify/tools.sdn")
expect(verify).to_contain("smoke_core")
expect(verify).to_contain("smoke_mcp")
```

</details>

#### renders pipe impl tools with target-specific tool sets

1. seed pipe tools
   - Expected: run_gen(["generate", "--root", impl_root]).exit_code equals `0`
2. seed pipe tools
   - Expected: run_gen(["generate", "--root", dev_root]).exit_code equals `0`
   - Expected: dev_has_duplicate_check is false
3. seed pipe tools
   - Expected: run_gen(["generate", "--root", refactor_root]).exit_code equals `0`
4. seed pipe tools
   - Expected: run_gen(["generate", "--root", loop_root]).exit_code equals `0`
   - Expected: loop_has_duplicate_check is false
5. seed pipe tools
   - Expected: run_gen(["generate", "--root", stitch_root]).exit_code equals `0`
   - Expected: stitch_has_duplicate_check is false
6. seed pipe tools
   - Expected: run_gen(["generate", "--root", sync_root]).exit_code equals `0`
   - Expected: sync_has_duplicate_check is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val impl_root = root("pipe_impl")
seed_pipe_tools(impl_root, "pipe_impl_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/tools.sdn")
expect(run_gen(["generate", "--root", impl_root]).exit_code).to_equal(0)
val impl_tools = read_file(impl_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/tools.sdn")
expect(impl_tools).to_contain("duplicate_check")
expect(impl_tools).to_contain("playwright")

val dev_root = root("pipe_impl_dev")
seed_pipe_tools(dev_root, "pipe_impl_dev_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/dev/tools.sdn")
expect(run_gen(["generate", "--root", dev_root]).exit_code).to_equal(0)
val dev = read_file(dev_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/dev/tools.sdn")
expect(dev).to_contain("playwright")
val dev_has_duplicate_check = dev.contains("duplicate_check")
expect(dev_has_duplicate_check).to_equal(false)

val refactor_root = root("pipe_impl_refactor")
seed_pipe_tools(refactor_root, "pipe_impl_refactor_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/refactor/tools.sdn")
expect(run_gen(["generate", "--root", refactor_root]).exit_code).to_equal(0)
val refactor = read_file(refactor_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/refactor/tools.sdn")
expect(refactor).to_contain("duplicate_check")
expect(refactor).to_contain("call sites")

val loop_root = root("pipe_impl_spipe_loop")
seed_pipe_tools(loop_root, "pipe_impl_spipe_loop_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/spipe_loop/tools.sdn")
expect(run_gen(["generate", "--root", loop_root]).exit_code).to_equal(0)
val loop_tools = read_file(loop_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/spipe_loop/tools.sdn")
expect(loop_tools).to_contain("failing specs")
val loop_has_duplicate_check = loop_tools.contains("duplicate_check")
expect(loop_has_duplicate_check).to_equal(false)

val stitch_root = root("pipe_impl_stitch")
seed_pipe_tools(stitch_root, "pipe_impl_stitch_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/stitch/tools.sdn")
expect(run_gen(["generate", "--root", stitch_root]).exit_code).to_equal(0)
val stitch = read_file(stitch_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/stitch/tools.sdn")
expect(stitch).to_contain("stitch_mcp")
val stitch_has_duplicate_check = stitch.contains("duplicate_check")
expect(stitch_has_duplicate_check).to_equal(false)

val sync_root = root("pipe_impl_sync")
seed_pipe_tools(sync_root, "pipe_impl_sync_tools", "impl", "doc/00_llm_process/skill_command/skills/pipe/impl/sync/tools.sdn")
expect(run_gen(["generate", "--root", sync_root]).exit_code).to_equal(0)
val sync_tools = read_file(sync_root + "/doc/00_llm_process/skill_command/skills/pipe/impl/sync/tools.sdn")
expect(sync_tools).to_contain("jj")
val sync_has_duplicate_check = sync_tools.contains("duplicate_check")
expect(sync_has_duplicate_check).to_equal(false)
```

</details>

#### creates skeleton experts once and preserves manual updates

1. seed skeleton
   - Expected: run_gen(["generate", "--root", r]).exit_code equals `0`
   - Expected: shell("printf '\\nManual note\\n' >> '" + path + "'").exit_code equals `0`
   - Expected: run_gen(["generate", "--force", "--root", r]).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("skeleton")
seed_skeleton(r)
expect(run_gen(["generate", "--root", r]).exit_code).to_equal(0)
val path = r + "/doc/00_llm_process/feature_expert/demo_feature/skill.md"
expect(read_file(path)).to_contain("# demo_feature")
expect(shell("printf '\\nManual note\\n' >> '" + path + "'").exit_code).to_equal(0)
expect(run_gen(["generate", "--force", "--root", r]).exit_code).to_equal(0)
expect(read_file(path)).to_contain("Manual note")
```

</details>

#### emits JSON drift status

1. seed
   - Expected: result.exit_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = root("json")
seed(r, "managed")
val result = run_gen(["check", "--root", r, "--json"])
expect(result.exit_code).to_equal(1)
expect(result.stdout).to_contain("\"ok\":false")
expect(result.stdout).to_contain("sample_doc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/llm_process/llm_process_gen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- llm-process-gen

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
