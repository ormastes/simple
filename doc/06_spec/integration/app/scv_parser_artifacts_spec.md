# Scv Parser Artifacts Specification

> Tests covering scv parser artifacts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Artifacts Specification

## Scenarios

### scv parser artifacts

#### records fallback parse metadata without blocking private history

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records fallback parse metadata without blocking private history


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records fallback parse metadata without blocking private history")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parse.XXXXXX)\nprintf 'fn broken(\\n' > \"$TMP/bad.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate bad.spl\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" log\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready || true\n"
val out = _run_parser_script(script)
expect(out).to_contain("snapshot commit_")
expect(out).to_contain("parser: fallback-line")
expect(out).to_contain("status: parsed_error")
expect(out).to_contain("syntax_")
expect(out).to_contain("semantic_")
expect(out).to_contain("runtime: pure-simple")
expect(out).to_contain("bad.spl|simple|sha256_")
expect(out).to_contain("|fallback-line|parsed_error|")
expect(out).to_contain("state=parsed_error")
expect(out).to_contain("ERROR current commit is not test_ok")
expect(out).to_contain("exit=0")
```

</details>

#### records distinct raw and policy-normalized parser hashes

- records distinct raw and policy-normalized parser hashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records distinct raw and policy-normalized parser hashes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-hashes.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nFIRST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index)\nprintf 'alpha   \\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index)\nFIRST_RAW=$(printf '%s\\n' \"$FIRST\" | awk -F'|' '{print $3}')\nFIRST_SEM=$(printf '%s\\n' \"$FIRST\" | awk -F'|' '{print $5}')\nSECOND_RAW=$(printf '%s\\n' \"$SECOND\" | awk -F'|' '{print $3}')\nSECOND_SEM=$(printf '%s\\n' \"$SECOND\" | awk -F'|' '{print $5}')\ntest \"$FIRST_RAW\" != \"$SECOND_RAW\"\ntest \"$FIRST_SEM\" = \"$SECOND_SEM\"\nprintf 'first=%s\\nsecond=%s\\n' \"$FIRST\" \"$SECOND\"\n"
val out = _run_parser_script(script)
expect(out).to_contain("a.txt|fallback|sha256_")
expect(out).to_contain("|syntax_")
expect(out).to_contain("|semantic_")
expect(out).to_contain("exit=0")
```

</details>

#### stores parser registry metadata and language overrides

- stores parser registry metadata and language overrides


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stores parser registry metadata and language overrides")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\n"
val out = _run_parser_script(script)
expect(out).to_contain("language: fallback-line")
expect(out).to_contain("langmap foo custom tree-sitter-custom 1.0.0")
expect(out).to_contain("foo|custom|tree-sitter-custom|1.0.0")
expect(out).to_contain("language: custom")
expect(out).to_contain("sample.foo|custom|sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### detects language from shebang when no extension mapping exists

- detects language from shebang when no extension mapping exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects language from shebang when no extension mapping exists")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-shebang.XXXXXX)\nprintf '#!/usr/bin/env python\\nprint(1)\\n' > \"$TMP/tool\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate tool\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\n"
val out = _run_parser_script(script)
expect(out).to_contain("language: python")
expect(out).to_contain("tool|python|sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe language mapping metadata

- rejects unsafe language mapping metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe language mapping metadata")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-reject.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set 'foo|bar' custom tree-sitter-custom 1.0.0)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("ERROR unsafe language mapping metadata")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### writes immutable fallback syntax node objects

- writes immutable fallback syntax node objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes immutable fallback syntax node objects")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-nodes.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ntest -n \"$ROOT\"\nsed -n '1,12p' \".scv/objects/syntax/$ROOT.sdn\"\nfind .scv/objects/syntax -type f | wc -l | tr -d ' '\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" db-index >/dev/null\ngrep '| syntax |' .scv/meta/object_index.sdn | head -1\n"
val out = _run_parser_script(script)
expect(out).to_contain("node: syntax_node_")
expect(out).to_contain("|node=syntax_node_")
expect(out).to_contain("grammar: fallback-line")
expect(out).to_contain("kind: file")
expect(out).to_contain("children: syntax_node_")
expect(out).to_contain("| syntax |")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects parser indexes with missing syntax nodes

- fsck rejects parser indexes with missing syntax nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects parser indexes with missing syntax nodes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-fsck.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nrm \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("missing syntax node: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### gc prunes unreachable syntax nodes while preserving parser-index nodes

- gc prunes unreachable syntax nodes while preserving parser-index nodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gc prunes unreachable syntax nodes while preserving parser-index nodes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-gc.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'grammar: orphan\\nchildren:\\n' > .scv/objects/syntax/syntax_node_orphan.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\ntest -e \".scv/objects/syntax/$ROOT.sdn\"\ntest ! -e .scv/objects/syntax/syntax_node_orphan.sdn\n"
val out = _run_parser_script(script)
expect(out).to_contain("unreachable_syntax=1")
expect(out).to_contain("pruned_syntax=1")
expect(out).to_contain("unreachable_syntax=0")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe parser index paths

- rejects unsafe parser index paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe parser index paths")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-unsafe-path.XXXXXX)\nprintf 'bad\\n' > \"$TMP/bad|name.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate 'bad|name.txt')\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("ERROR unsafe path for SCV metadata: bad|name.txt")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_parser_artifacts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv parser artifacts.
- scv parser artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `7c544e72252ee09ff24b8224058c67642e282e62f3162e22698ef691f6443a92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c544e72252ee09ff24b8224058c67642e282e62f3162e22698ef691f6443a92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c544e72252ee09ff24b8224058c67642e282e62f3162e22698ef691f6443a92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_parser_artifacts_spec.spl
mirror: doc/06_spec/integration/app/scv_parser_artifacts_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_parser_artifacts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_parser_artifacts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_parser_artifacts_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records fallback parse metadata without blocking private history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_artifacts_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records distinct raw and policy-normalized parser hashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_artifacts_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores parser registry metadata and language overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
