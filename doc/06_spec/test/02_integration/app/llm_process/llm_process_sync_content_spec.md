# Llm Process Sync Content Specification

> <details>

<!-- sdn-diagram:id=llm_process_sync_content_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_process_sync_content_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_process_sync_content_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_process_sync_content_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Process Sync Content Specification

## Scenarios

### LLM process sync content

#### does not reference the retired git-jj-sync command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("! rg -n '/git-jj-sync|git-jj-sync' doc/00_llm_process .codex/skills .agents/skills .gemini/commands .claude/commands")
expect(result.exit_code).to_equal(0)
```

</details>

#### stops file-count reduction blocks before any push

1. "roots=[Path
2. "    if not root exists
3. "    for p in root rglob
4. "        if not p is file
5. "        text=p read text
6. "            i=text find
7. "            push=text find
8. "            stop=text find
9. "            if push >= 0 and
10. "    print
11. "    raise SystemExit
   - Expected: shell(script).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "python3 - <<'PY'\n" +
    "from pathlib import Path\n" +
    "roots=[Path('doc/00_llm_process'),Path('.codex/skills'),Path('.agents/skills'),Path('.gemini/commands'),Path('.claude/commands')]\n" +
    "bad=[]\n" +
    "for root in roots:\n" +
    "    if not root.exists(): continue\n" +
    "    for p in root.rglob('*'):\n" +
    "        if not p.is_file(): continue\n" +
    "        text=p.read_text(errors='ignore')\n" +
    "        i=0\n" +
    "        while True:\n" +
    "            i=text.find('File count reduced', i)\n" +
    "            if i < 0: break\n" +
    "            push=text.find('jj git push', i)\n" +
    "            stop=text.find('exit 1', i)\n" +
    "            if push >= 0 and (stop < 0 or stop > push): bad.append(str(p))\n" +
    "            i += 1\n" +
    "if bad:\n" +
    "    print('\\n'.join(sorted(set(bad))))\n" +
    "    raise SystemExit(1)\n" +
    "PY"
expect(shell(script).exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/llm_process/llm_process_sync_content_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM process sync content

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
