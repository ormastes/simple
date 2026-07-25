# Scv Gates Specification

> <details>

<!-- sdn-diagram:id=scv_gates_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_gates_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_gates_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_gates_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Gates Specification

## Scenarios

### scv gates

#### promotes commits through compile, test, and public-ready gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-gates.XXXXXX)\nprintf 'ok\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBASE=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)\nBASE_CHANGE=$(sed -n 's/change: //p' \".scv/objects/commits/$BASE.sdn\")\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" compile-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\nCURRENT=$(sed -n 's/default: //p' .scv/meta/workspaces.sdn)\nCURRENT_CHANGE=$(sed -n 's/change: //p' \".scv/objects/commits/$CURRENT.sdn\")\nLATEST=$(sed -n 's/latest: //p' \".scv/objects/changes/$CURRENT_CHANGE.sdn\")\ntest \"$BASE_CHANGE\" = \"$CURRENT_CHANGE\"\ntest \"$LATEST\" = \"$CURRENT\"\nprintf 'change_stable=%s\\nlatest=%s\\ncurrent=%s\\n' \"$CURRENT_CHANGE\" \"$LATEST\" \"$CURRENT\"\n"
val out = _run_gates_script(script)
expect(out).to_contain("state=compile_ok")
expect(out).to_contain("state=test_ok")
expect(out).to_contain("state=public_ready")
expect(out).to_contain("change_stable=change_")
expect(out).to_contain("latest=commit_")
expect(out).to_contain("current=commit_")
expect(out).to_contain("exit=0")
```

</details>

#### exposes parsed_error and rejects unknown commit states

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-state-validation.XXXXXX)\nprintf 'bad\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" mark-state parsed_error >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" mark-state nonsense)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("state=parsed_error")
expect(out).to_contain("ERROR invalid state")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects gate promotion when current workspace metadata is corrupt

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-gate-workspace-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nGOOD_OP=$(cat .scv/HEAD_OP)\nCOMMITS_BEFORE=$(find .scv/objects/commits -type f | wc -l)\nprintf 'default: commit_missing\\n' > .scv/meta/workspaces.sdn\nset +e\nBAD_COMPILE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" compile-gate true)\nBAD_COMPILE_CODE=$?\nBAD_MARK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" mark-state test_ok)\nBAD_MARK_CODE=$?\nset -e\nCOMMITS_AFTER=$(find .scv/objects/commits -type f | wc -l)\nprintf '%s\\nbad_compile_code=%s\\n%s\\nbad_mark_code=%s\\nhead_same=%s\\ncommits_same=%s\\n' \"$BAD_COMPILE\" \"$BAD_COMPILE_CODE\" \"$BAD_MARK\" \"$BAD_MARK_CODE\" \"$([ \"$(cat .scv/HEAD_OP)\" = \"$GOOD_OP\" ] && printf yes || printf no)\" \"$([ \"$COMMITS_BEFORE\" = \"$COMMITS_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_COMPILE_CODE\" -ne 0\ntest \"$BAD_MARK_CODE\" -ne 0\ntest \"$(cat .scv/HEAD_OP)\" = \"$GOOD_OP\"\ntest \"$COMMITS_BEFORE\" = \"$COMMITS_AFTER\"\n"
val out = _run_gates_script(script)
expect(out).to_contain("ERROR invalid workspace parent")
expect(out).to_contain("bad_compile_code=1")
expect(out).to_contain("bad_mark_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("commits_same=yes")
expect(out).to_contain("exit=0")
```

</details>

#### exports public artifacts only after public_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-export.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-public-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\"\ncat \"$PUB/publish.sdn\"\ncat \"$PUB/manifest.sdn\"\nsed -n '1,14p' \"$PUB/export.fi\"\nprintf 'files=%s\\n' \"$(find \"$PUB\" -type f | wc -l | tr -d ' ')\"\nprintf 'broken\\n' > \"$PUB/export.fi\"\nset +e\nBROKEN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBROKEN_CODE=$?\nset -e\nprintf '%s\\nbroken_code=%s\\n' \"$BROKEN\" \"$BROKEN_CODE\"\ntest \"$BROKEN_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("ERROR public-export requires public_ready")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("public-export /tmp/scv-public-out.")
expect(out).to_contain("public-export-verify /tmp/scv-public-out.")
expect(out).to_contain("format: scv-public-export-v1")
expect(out).to_contain("state: public_ready")
expect(out).to_contain("format: scv-export-manifest-v1")
expect(out).to_contain("commit refs/heads/main")
expect(out).to_contain("files=3")
expect(out).to_contain("ERROR public-export stream branch mismatch")
expect(out).to_contain("broken_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public export markers whose ids, state, or branch are unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-export-state.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-public-state-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nset +e\nBAD_EXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" 'bad|branch')\nBAD_EXPORT_CODE=$?\nset -e\nprintf '%s\\nbad_export_code=%s\\n' \"$BAD_EXPORT\" \"$BAD_EXPORT_CODE\"\ntest \"$BAD_EXPORT_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncp \"$PUB/publish.sdn\" \"$PUB/publish.good\"\nsed 's/state: public_ready/state: test_ok/' \"$PUB/publish.good\" > \"$PUB/publish.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\nsed 's/branch: main/branch: bad|branch/' \"$PUB/publish.good\" > \"$PUB/publish.sdn\"\nset +e\nBAD_BRANCH=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_BRANCH_CODE=$?\nset -e\nprintf '%s\\nbad_branch_code=%s\\n' \"$BAD_BRANCH\" \"$BAD_BRANCH_CODE\"\ntest \"$BAD_BRANCH_CODE\" -ne 0\nsed 's/commit: commit_/commit: bad|commit_/' \"$PUB/publish.good\" > \"$PUB/publish.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/tree: tree_/tree: bad|tree_/' \"$PUB/publish.good\" > \"$PUB/publish.sdn\"\nset +e\nBAD_TREE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_TREE_CODE=$?\nset -e\nprintf '%s\\nbad_tree_code=%s\\n' \"$BAD_TREE\" \"$BAD_TREE_CODE\"\ntest \"$BAD_TREE_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("bad_export_code=1")
expect(out).to_contain("ERROR public-export marker state is not public_ready")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("ERROR unsafe public branch")
expect(out).to_contain("bad_branch_code=1")
expect(out).to_contain("ERROR unsafe public-export commit id")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR unsafe public-export tree id")
expect(out).to_contain("bad_tree_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public export manifests that disagree with the marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-export-manifest-marker.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-public-manifest-marker-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncp \"$PUB/manifest.sdn\" \"$PUB/manifest.good\"\nsed 's/commit: commit_/commit: commit_bad/' \"$PUB/manifest.good\" > \"$PUB/manifest.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/tree: tree_/tree: tree_bad/' \"$PUB/manifest.good\" > \"$PUB/manifest.sdn\"\nset +e\nBAD_TREE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_TREE_CODE=$?\nset -e\nprintf '%s\\nbad_tree_code=%s\\n' \"$BAD_TREE\" \"$BAD_TREE_CODE\"\ntest \"$BAD_TREE_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("ERROR public-export manifest commit mismatch")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR public-export manifest tree mismatch")
expect(out).to_contain("bad_tree_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### verifies public export file commands outside fast-import data payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-export-data-skip.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-public-data-skip-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 8\npayload\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 23\nM 100644 :999 ghost.txt\nM 100644 :1 a.txt\nEOF\nVERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nprintf '%s\\n' \"$VERIFY\"\n"
val out = _run_gates_script(script)
expect(out).to_contain("public-export-verify /tmp/scv-public-data-skip-out.")
expect(out).to_contain("files=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public export streams with unsafe fast-import file commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-export-bad-command.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-public-bad-command-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncp \"$PUB/export.fi\" \"$PUB/export.good\"\nsed 's/M 100644/M 120000/' \"$PUB/export.good\" > \"$PUB/export.fi\"\nset +e\nBAD_MODE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_MODE_CODE=$?\nset -e\nmv \"$PUB/export.good\" \"$PUB/export.fi\"\nsed 's/:1 a.txt/:999 a.txt/' \"$PUB/export.fi\" > \"$PUB/export.tmp\"\nmv \"$PUB/export.tmp\" \"$PUB/export.fi\"\nset +e\nBAD_MARK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_MARK_CODE=$?\nset -e\nmv \"$PUB/export.good\" \"$PUB/export.fi\"\nsed 's/a.txt/bad|name.txt/' \"$PUB/export.fi\" > \"$PUB/export.tmp\"\nmv \"$PUB/export.tmp\" \"$PUB/export.fi\"\nset +e\nBAD_PATH=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_PATH_CODE=$?\nset -e\nprintf '%s\\nbad_mode_code=%s\\n%s\\nbad_mark_code=%s\\n%s\\nbad_path_code=%s\\n' \"$BAD_MODE\" \"$BAD_MODE_CODE\" \"$BAD_MARK\" \"$BAD_MARK_CODE\" \"$BAD_PATH\" \"$BAD_PATH_CODE\"\ntest \"$BAD_MODE_CODE\" -ne 0\ntest \"$BAD_MARK_CODE\" -ne 0\ntest \"$BAD_PATH_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("ERROR unsupported fast-import file mode: 120000")
expect(out).to_contain("bad_mode_code=1")
expect(out).to_contain("ERROR missing fast-import blob mark: 999")
expect(out).to_contain("bad_mark_code=1")
expect(out).to_contain("ERROR unsafe fast-import path: bad|name.txt")
expect(out).to_contain("bad_path_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### pushes public artifacts to a filesystem remote only after public_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-public-push.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-remote.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main\ncat \"$REMOTE/refs.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$REMOTE/branches/main\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main\ncp \"$REMOTE/refs.sdn\" \"$REMOTE/refs.good\"\nsed 's/commit_[^|]*/commit_broken/' \"$REMOTE/refs.good\" > \"$REMOTE/refs.sdn\"\nset +e\nBROKEN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main)\nBROKEN_CODE=$?\nset -e\nprintf '%s\\nbroken_code=%s\\n' \"$BROKEN\" \"$BROKEN_CODE\"\ntest \"$BROKEN_CODE\" -ne 0\nmv \"$REMOTE/refs.good\" \"$REMOTE/refs.sdn\"\nset +e\nUNSAFE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" 'bad|branch')\nUNSAFE_CODE=$?\nset -e\nprintf '%s\\nunsafe_code=%s\\n' \"$UNSAFE\" \"$UNSAFE_CODE\"\ntest \"$UNSAFE_CODE\" -ne 0\n"
val out = _run_gates_script(script)
expect(out).to_contain("ERROR public-export requires public_ready")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("public-push /tmp/scv-public-remote.")
expect(out).to_contain("format: scv-remote-refs-v1")
expect(out).to_contain("main|commit_")
expect(out).to_contain("public-export-verify /tmp/scv-public-remote.")
expect(out).to_contain("public-push-verify /tmp/scv-public-remote.")
expect(out).to_contain("ERROR public remote commit mismatch")
expect(out).to_contain("broken_code=1")
expect(out).to_contain("ERROR unsafe public branch")
expect(out).to_contain("unsafe_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_gates_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
