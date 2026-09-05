# Scv Langmap Safety Specification

> <details>

<!-- sdn-diagram:id=scv_langmap_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_langmap_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_langmap_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_langmap_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Langmap Safety Specification

## Scenarios

### scv langmap safety

#### rejects malformed language mapping rows during parse and fsck

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-bad-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\nsed 's/$/|extra/' .scv/meta/langmap.sdn > .scv/meta/langmap.bad\nmv .scv/meta/langmap.bad .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR bad language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("bad language mapping entry:")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### does not reuse parser cache after langmap rows become malformed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-cache-bad-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nsed 's/$/|extra/' .scv/meta/langmap.sdn > .scv/meta/langmap.bad\nmv .scv/meta/langmap.bad .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\ncase \"$BAD_PARSE\" in *'cache: reused'*) exit 7;; esac\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR bad language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate language mapping rows during parse and fsck

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-duplicate-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\ncat .scv/meta/langmap.sdn >> .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR duplicate language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("duplicate language mapping entry: foo")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_langmap_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv langmap safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
