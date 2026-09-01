# Llm Process Sync Content Specification

> Tests covering LLM process sync content.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Process Sync Content Specification

## Scenarios

### LLM process sync content

#### does not reference the retired git-jj-sync command

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not reference the retired git-jj-sync command
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not reference the retired git-jj-sync command")
val result = shell("! rg -n '/git-jj-sync|git-jj-sync' doc/00_llm_process .codex/skills .agents/skills .gemini/commands .claude/commands")
expect(result.exit_code).to_equal(0)
```

</details>

#### stops file-count reduction blocks before any push

- stops file-count reduction blocks before any push
   - Expected: shell(script).exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stops file-count reduction blocks before any push")
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
| Source | `test/integration/app/llm_process/llm_process_sync_content_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM process sync content.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d057dbfd639313000ec979a7f9e9bc630d16f46ff6f770f75ee33a4dfe29ff5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d057dbfd639313000ec979a7f9e9bc630d16f46ff6f770f75ee33a4dfe29ff5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d057dbfd639313000ec979a7f9e9bc630d16f46ff6f770f75ee33a4dfe29ff5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/app/llm_process/llm_process_sync_content_spec.spl
mirror: doc/06_spec/integration/app/llm_process/llm_process_sync_content_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/llm_process/llm_process_sync_content_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/llm_process/llm_process_sync_content_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/llm_process/llm_process_sync_content_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/llm_process/llm_process_sync_content_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not reference the retired git-jj-sync command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/llm_process/llm_process_sync_content_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stops file-count reduction blocks before any push' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
