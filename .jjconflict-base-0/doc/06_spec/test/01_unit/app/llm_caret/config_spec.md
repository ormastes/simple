# Config Specification

> <details>

<!-- sdn-diagram:id=config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Specification

## Scenarios

### Config Defaults

#### has default provider

- reset config
   - Expected: DEFAULT_PROVIDER equals `claude_cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(DEFAULT_PROVIDER).to_equal("claude_cli")
```

</details>

#### has default history file

- reset config
   - Expected: DEFAULT_HISTORY_FILE equals `.llm_caret_history.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(DEFAULT_HISTORY_FILE).to_equal(".llm_caret_history.sdn")
```

</details>

#### has default max history

- reset config
   - Expected: DEFAULT_MAX_HISTORY equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(DEFAULT_MAX_HISTORY).to_equal(100)
```

</details>

#### has default claude cli path

- reset config
   - Expected: CLAUDE_CLI_PATH equals `claude`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(CLAUDE_CLI_PATH).to_equal("claude")
```

</details>

#### has default claude cli model

- reset config
   - Expected: CLAUDE_CLI_MODEL equals `claude-sonnet-4-20250514`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(CLAUDE_CLI_MODEL).to_equal("claude-sonnet-4-20250514")
```

</details>

#### has default opencode cli path

- reset config
   - Expected: OPENCODE_CLI_PATH equals `opencode`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(OPENCODE_CLI_PATH).to_equal("opencode")
```

</details>

#### has default claude api base url

- reset config
   - Expected: CLAUDE_API_BASE_URL equals `https://api.anthropic.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(CLAUDE_API_BASE_URL).to_equal("https://api.anthropic.com")
```

</details>

#### has default openai base url

- reset config
   - Expected: OPENAI_BASE_URL equals `https://api.openai.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(OPENAI_BASE_URL).to_equal("https://api.openai.com")
```

</details>

#### has default openai model

- reset config
   - Expected: OPENAI_MODEL equals `gpt-4o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(OPENAI_MODEL).to_equal("gpt-4o")
```

</details>

#### has default compat base url

- reset config
   - Expected: COMPAT_BASE_URL equals `http://localhost:11434`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(COMPAT_BASE_URL).to_equal("http://localhost:11434")
```

</details>

#### has default local python path

- reset config
   - Expected: LOCAL_PYTHON_PATH equals `python3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_config()
expect(LOCAL_PYTHON_PATH).to_equal("python3")
```

</details>

### Config Parsing

#### parses defaults section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_defaults())
```

</details>

#### parses claude_cli section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_claude_cli())
```

</details>

#### parses opencode_cli section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_opencode_cli())
```

</details>

#### parses claude_api section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_claude_api())
```

</details>

#### parses openai section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_openai())
```

</details>

#### parses openai_compat section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_openai_compat())
```

</details>

#### parses local_torch section

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_local_torch())
```

</details>

#### skips comments and empty lines

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_skips_comments())
```

</details>

#### parses multiple sections

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_parse_multiple_sections())
```

</details>

#### sets config loaded flag

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_config_loaded_flag())
```

</details>

#### handles empty config

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(_test_empty_config())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Config Defaults
- Config Parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
