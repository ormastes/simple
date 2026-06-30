# Scv Diff Specification

> <details>

<!-- sdn-diagram:id=scv_diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_diff_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Diff Specification

## Scenarios

### scv diff

#### supports raw, syntax, and formatting policy diff views

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-policy.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\nprintf 'gone\\n' > \"$TMP/delete.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha   \\nbeta\\t\\n' > a.txt\nRAW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nSYN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --syntax)\nIGN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-trailing-space)\nFMT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf 'raw=%s\\n' \"$RAW\"\nprintf 'syntax=%s\\n' \"$SYN\"\nprintf 'ignore=%s\\n' \"$IGN\"\nprintf 'format=%s\\n' \"$FMT\"\ncase \"$IGN\" in *'modified a.txt'*) exit 7;; esac\ncase \"$FMT\" in *'modified a.txt'*) exit 8;; esac\nrm delete.txt\nprintf 'gamma\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting\n"
val out = _run_diff_script(script)
expect(out).to_contain("raw=modified a.txt")
expect(out).to_contain("syntax=modified a.txt")
expect(out).to_contain("ignore=no changes")
expect(out).to_contain("format=no changes")
expect(out).to_contain("deleted delete.txt")
expect(out).to_contain("exit=0")
```

</details>

#### detects exact-content renames before add-delete output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-rename.XXXXXX)\nprintf 'payload\\n' > \"$TMP/old.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nmv old.txt new.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'added new.txt'*) exit 7;; esac\ncase \"$OUT\" in *'deleted old.txt'*) exit 8;; esac\n"
val out = _run_diff_script(script)
expect(out).to_contain("renamed old.txt -> new.txt")
expect(out).to_contain("exit=0")
```

</details>

#### keeps formatting ignore language-sensitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-format-policy.XXXXXX)\nprintf 'alpha beta\\n' > \"$TMP/a.txt\"\nprintf 'if ok:\\n    run()\\n' > \"$TMP/code.py\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha      beta\\n' > a.txt\nprintf 'if ok:\\nrun()\\n' > code.py\nRAW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nFMT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf 'raw=%s\\n' \"$RAW\"\nprintf 'format=%s\\n' \"$FMT\"\ncase \"$FMT\" in *'modified a.txt'*) exit 7;; esac\n"
val out = _run_diff_script(script)
expect(out).to_contain("raw=modified a.txt")
expect(out).to_contain("modified code.py")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv diff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
