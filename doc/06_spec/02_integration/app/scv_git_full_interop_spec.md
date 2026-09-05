# scv_git_full_interop_spec

> Validates that merge commits (commits with two or more parent IDs) are

<!-- sdn-diagram:id=scv_git_full_interop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_git_full_interop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_git_full_interop_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_git_full_interop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_git_full_interop_spec

Validates that merge commits (commits with two or more parent IDs) are

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_git_full_interop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Multi-Parent Merge Commit Import/Export

    Validates that merge commits (commits with two or more parent IDs) are
    correctly imported from a git-fast-import stream and re-exported with
    both `from` and `merge` lines so that git can reconstruct the DAG.

    AC-4 item: "Multi-parent commits … round-trip against Git fixtures"

## Scenarios

### scv git full interop: multi-parent merge commits

#### imports a fast-import stream with a merge commit and stores both parents

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-multi-parent-import.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > merge.fi <<'EOF'\nblob\nmark :1\ndata 5\nalpha\nblob\nmark :2\ndata 5\nbeta\nblob\nmark :3\ndata 6\nmerge\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 7\ncommit1\nM 100644 :1 a.txt\ncommit refs/heads/feature\nmark :11\ncommitter Dev <dev@example.invalid> 1000000001 +0000\ndata 7\ncommit2\nfrom :10\nM 100644 :2 b.txt\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 1000000002 +0000\ndata 5\nmerge\nfrom :10\nmerge :11\nM 100644 :3 m.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import merge.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'mtxt=%s\\n' \"$(cat out/m.txt | tr '\\n' '|')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("import-git-fast-import")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("mtxt=merge|")
expect(out).to_contain("exit=0")
```

</details>

#### exports a merge commit with both from and merge lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-multi-parent-export.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-multi-parent-export-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > merge.fi <<'EOF'\nblob\nmark :1\ndata 5\nalpha\nblob\nmark :2\ndata 5\nbeta\nblob\nmark :3\ndata 6\nmerge\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 7\ncommit1\nM 100644 :1 a.txt\ncommit refs/heads/feature\nmark :11\ncommitter Dev <dev@example.invalid> 1000000001 +0000\ndata 7\ncommit2\nfrom :10\nM 100644 :2 b.txt\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 1000000002 +0000\ndata 5\nmerge\nfrom :10\nmerge :11\nM 100644 :3 m.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import merge.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\nprintf 'merge_lines=%s\\n' \"$(grep -c '^merge ' out.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/out.fi\" >/dev/null\ngit checkout -q main\nprintf 'mtxt=%s\\n' \"$(cat m.txt | tr '\\n' '|')\"\nprintf 'parents=%s\\n' \"$(git log --pretty=format:'%P' -1 HEAD | wc -w | tr -d ' ')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("merge_lines=1")
expect(out).to_contain("mtxt=merge|")
expect(out).to_contain("parents=2")
expect(out).to_contain("exit=0")
```

</details>

#### preserves change-id stability rule for merge commits (change-merge: prefix)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-multi-parent-changeid.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > merge.fi <<'EOF'\nblob\nmark :1\ndata 2\nA\nblob\nmark :2\ndata 2\nB\nblob\nmark :3\ndata 2\nC\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 2\nC1\nM 100644 :1 a.txt\ncommit refs/heads/feat\nmark :11\ncommitter Dev <dev@example.invalid> 2 +0000\ndata 2\nC2\nfrom :10\nM 100644 :2 b.txt\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 3 +0000\ndata 2\nMG\nfrom :10\nmerge :11\nM 100644 :3 c.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import merge.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log main\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("change-merge:")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: tag objects

#### imports a lightweight tag via reset refs/tags/ and resolves it

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-lightweight-tag.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > lwtag.fi <<'EOF'\nblob\nmark :1\ndata 7\npayload\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 8\nbase-cmt\nM 100644 :1 a.txt\nreset refs/tags/v1.0\nfrom :10\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import lwtag.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" tag-list\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("import-git-fast-import")
expect(out).to_contain("v1.0")
expect(out).to_contain("exit=0")
```

</details>

#### exports a lightweight tag as a reset refs/tags/ line in the stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-lwtag-export.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-lwtag-export-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > lwtag.fi <<'EOF'\nblob\nmark :1\ndata 7\npayload\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 8\nbase-cmt\nM 100644 :1 a.txt\nreset refs/tags/v1.0\nfrom :10\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import lwtag.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\nprintf 'reset_tag=%s\\n' \"$(grep -c '^reset refs/tags/' out.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/out.fi\" >/dev/null\nprintf 'tag_target=%s\\n' \"$(git rev-parse --verify refs/tags/v1.0 2>/dev/null | wc -c | tr -d ' ')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("reset_tag=1")
expect(out).to_contain("exit=0")
```

</details>

#### imports an annotated tag record and stores tagger and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-annotated-tag.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > atag.fi <<'EOF'\nblob\nmark :1\ndata 7\npayload\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 8\nbase-cmt\nM 100644 :1 a.txt\ntag v2.0\nfrom :10\ntagger Releaser <rel@example.invalid> 1000000099 +0000\ndata 18\nRelease version 2.0\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import atag.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" tag-list\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("import-git-fast-import")
expect(out).to_contain("v2.0")
expect(out).to_contain("exit=0")
```

</details>

#### exports an annotated tag as a tag record with tagger and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-annotated-tag-export.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-annotated-tag-export-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > atag.fi <<'EOF'\nblob\nmark :1\ndata 7\npayload\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 8\nbase-cmt\nM 100644 :1 a.txt\ntag v2.0\nfrom :10\ntagger Releaser <rel@example.invalid> 1000000099 +0000\ndata 18\nRelease version 2.0\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import atag.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\nprintf 'tag_record=%s\\n' \"$(grep -c '^tag v2.0' out.fi || echo 0)\"\nprintf 'tagger_line=%s\\n' \"$(grep -c '^tagger ' out.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/out.fi\" >/dev/null\nprintf 'annotated_ok=%s\\n' \"$(git cat-file -t refs/tags/v2.0 2>/dev/null || echo none)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("tag_record=1")
expect(out).to_contain("tagger_line=1")
expect(out).to_contain("annotated_ok=tag")
expect(out).to_contain("exit=0")
```

</details>

#### rejects a tag name that fails ref safety validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bad-tag-name.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > badtag.fi <<'EOF'\nblob\nmark :1\ndata 4\ndata\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 4\ncmt1\nM 100644 :1 a.txt\ntag bad..tag\nfrom :10\ntagger Dev <dev@example.invalid> 1 +0000\ndata 4\nbad!\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import badtag.fi 2>&1)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: author and committer metadata

#### preserves distinct author and committer lines through import and export

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-author-committer.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-author-committer-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > acmeta.fi <<'EOF'\nblob\nmark :1\ndata 7\npayload\ncommit refs/heads/main\nmark :10\nauthor Original Author <author@example.invalid> 1000000000 +0200\ncommitter Build Bot <bot@example.invalid> 1000000100 +0000\ndata 12\nadd payload\nM 100644 :1 a.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import acmeta.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\nprintf 'author_line=%s\\n' \"$(grep -c '^author Original Author' out.fi || echo 0)\"\nprintf 'committer_line=%s\\n' \"$(grep -c '^committer Build Bot' out.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/out.fi\" >/dev/null\ngit checkout -q main\nprintf 'git_author=%s\\n' \"$(git log --pretty=format:'%an' -1)\"\nprintf 'git_committer=%s\\n' \"$(git log --pretty=format:'%cn' -1)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("author_line=1")
expect(out).to_contain("committer_line=1")
expect(out).to_contain("git_author=Original Author")
expect(out).to_contain("git_committer=Build Bot")
expect(out).to_contain("exit=0")
```

</details>

#### preserves author timestamp and timezone offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-author-tz.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > tztest.fi <<'EOF'\nblob\nmark :1\ndata 2\nX\ncommit refs/heads/main\nmark :10\nauthor TZTest <tz@example.invalid> 1234567890 -0530\ncommitter TZTest <tz@example.invalid> 1234567890 -0530\ndata 6\ntz-cmt\nM 100644 :1 x.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import tztest.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\nprintf 'tz_present=%s\\n' \"$(grep -c '\\-0530' out.fi || echo 0)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("tz_present=2")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: inline blob

#### imports an inline blob and stores file content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-inline-blob.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > inline.fi <<'EOF'\ncommit refs/heads/main\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 12\nadd inline\nM 100644 inline hello.txt\ndata 12\nhello world\n\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import inline.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'content=%s\\n' \"$(cat out/hello.txt | tr '\\n' '|')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("import-git-fast-import")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("content=hello world|")
expect(out).to_contain("exit=0")
```

</details>

#### imports multiple inline blobs in one commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-multi-inline.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > multi_inline.fi <<'EOF'\ncommit refs/heads/main\ncommitter Dev <dev@example.invalid> 1000000000 +0000\ndata 13\nmulti-inline\nM 100644 inline file1.txt\ndata 3\nfoo\nM 100644 inline file2.txt\ndata 3\nbar\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import multi_inline.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'f1=%s\\n' \"$(cat out/file1.txt | tr '\\n' '|')\"\nprintf 'f2=%s\\n' \"$(cat out/file2.txt | tr '\\n' '|')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("f1=foo|")
expect(out).to_contain("f2=bar|")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: reset command

#### updates a branch pointer via reset refs/heads without creating a commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-reset-heads.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > reset_heads.fi <<'EOF'\nblob\nmark :1\ndata 4\none\nblob\nmark :2\ndata 4\ntwo\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 2\nC1\nM 100644 :1 a.txt\ncommit refs/heads/old\nmark :11\ncommitter Dev <dev@example.invalid> 2 +0000\ndata 2\nC2\nfrom :10\nM 100644 :2 b.txt\nreset refs/heads/main\nfrom :11\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import reset_heads.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'btxt=%s\\n' \"$(cat out/b.txt | tr '\\n' '|')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("import-git-fast-import")
expect(out).to_contain("btxt=two|")
expect(out).to_contain("exit=0")
```

</details>

#### creates a lightweight tag via reset refs/tags/

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-reset-tags.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > reset_tags.fi <<'EOF'\nblob\nmark :1\ndata 3\nhi\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 4\ncmt1\nM 100644 :1 x.txt\nreset refs/tags/rel-1\nfrom :10\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import reset_tags.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" tag-list\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("rel-1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects reset with a missing from target for heads

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-reset-no-from.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > noreset.fi <<'EOF'\nreset refs/heads/ghost\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import noreset.fi 2>&1)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: parent-aware incremental export

#### exports only commits after the since commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-incremental-export.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-incremental-export-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > base.fi <<'EOF'\nblob\nmark :1\ndata 4\nbase\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 2\nC1\nM 100644 :1 base.txt\nblob\nmark :2\ndata 4\nsec2\ncommit refs/heads/main\nmark :11\ncommitter Dev <dev@example.invalid> 2 +0000\ndata 2\nC2\nfrom :10\nM 100644 :2 two.txt\nblob\nmark :3\ndata 5\nthird\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 3 +0000\ndata 2\nC3\nfrom :11\nM 100644 :3 three.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import base.fi >/dev/null\nC1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log main | grep commit_id | head -3 | tail -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import incr.fi main --since \"$C1\"\nprintf 'commit_count=%s\\n' \"$(grep -c '^commit ' incr.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/incr.fi\" >/dev/null 2>&1 || true\nprintf 'incr_file_ok=%s\\n' \"$(test -s \"$TMP/incr.fi\" && echo yes || echo no)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("commit_count=2")
expect(out).to_contain("incr_file_ok=yes")
expect(out).to_contain("exit=0")
```

</details>

#### full export when since is empty emits all commits

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-full-export-since-empty.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > three.fi <<'EOF'\nblob\nmark :1\ndata 2\nA\nblob\nmark :2\ndata 2\nB\nblob\nmark :3\ndata 2\nC\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 2\nC1\nM 100644 :1 a.txt\ncommit refs/heads/main\nmark :11\ncommitter Dev <dev@example.invalid> 2 +0000\ndata 2\nC2\nfrom :10\nM 100644 :2 b.txt\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 3 +0000\ndata 2\nC3\nfrom :11\nM 100644 :3 c.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import three.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import all.fi main\nprintf 'commit_count=%s\\n' \"$(grep -c '^commit ' all.fi || echo 0)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("commit_count=3")
expect(out).to_contain("exit=0")
```

</details>

#### incremental export of a merge commit includes both parents in the stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-incr-merge-export.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-incr-merge-export-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > dag.fi <<'EOF'\nblob\nmark :1\ndata 4\nbase\nblob\nmark :2\ndata 5\nfeat1\nblob\nmark :3\ndata 2\nM\ncommit refs/heads/main\nmark :10\ncommitter Dev <dev@example.invalid> 1 +0000\ndata 4\nbase\nM 100644 :1 base.txt\ncommit refs/heads/feature\nmark :11\ncommitter Dev <dev@example.invalid> 2 +0000\ndata 5\nfeat1\nfrom :10\nM 100644 :2 feat.txt\ncommit refs/heads/main\nmark :12\ncommitter Dev <dev@example.invalid> 3 +0000\ndata 5\nmerge\nfrom :10\nmerge :11\nM 100644 :3 m.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import dag.fi >/dev/null\nC_BASE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log main | grep commit_id | tail -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import incr_merge.fi main --since \"$C_BASE\"\nprintf 'merge_line=%s\\n' \"$(grep -c '^merge ' incr_merge.fi || echo 0)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/incr_merge.fi\" >/dev/null 2>&1 || true\nprintf 'stream_nonempty=%s\\n' \"$(test -s \"$TMP/incr_merge.fi\" && echo yes || echo no)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("merge_line=1")
expect(out).to_contain("stream_nonempty=yes")
expect(out).to_contain("exit=0")
```

</details>

### scv git full interop: round-trip fidelity

#### round-trips a single-branch linear history through git

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-roundtrip-linear.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-roundtrip-linear-git.XXXXXX)\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > in.fi <<'EOF'\nblob\nmark :1\ndata 5\nhello\nblob\nmark :2\ndata 5\nworld\ncommit refs/heads/main\nmark :10\nauthor Alice <alice@example.invalid> 1000000001 +0000\ncommitter Alice <alice@example.invalid> 1000000001 +0000\ndata 10\nadd hello\nM 100644 :1 hello.txt\ncommit refs/heads/main\nmark :11\nauthor Bob <bob@example.invalid> 1000000002 +0100\ncommitter Bob <bob@example.invalid> 1000000002 +0100\ndata 9\nadd world\nfrom :10\nM 100644 :2 world.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import in.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$SRC/out.fi\" >/dev/null\ngit checkout -q main\nprintf 'hello=%s\\n' \"$(cat hello.txt | tr '\\n' '|')\"\nprintf 'world=%s\\n' \"$(cat world.txt | tr '\\n' '|')\"\nprintf 'commits=%s\\n' \"$(git log --oneline | wc -l | tr -d ' ')\"\nprintf 'author0=%s\\n' \"$(git log --pretty=format:'%an' | head -1)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("hello=hello|")
expect(out).to_contain("world=world|")
expect(out).to_contain("commits=2")
expect(out).to_contain("author0=Bob")
expect(out).to_contain("exit=0")
```

</details>

#### round-trips a merge commit DAG with annotated tag through git

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-roundtrip-merge-tag.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-roundtrip-merge-tag-git.XXXXXX)\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > complex.fi <<'EOF'\nblob\nmark :1\ndata 4\nbase\nblob\nmark :2\ndata 6\nfeatX\nblob\nmark :3\ndata 3\nMRG\ncommit refs/heads/main\nmark :10\nauthor Dev1 <dev1@example.invalid> 1000 +0000\ncommitter Dev1 <dev1@example.invalid> 1000 +0000\ndata 4\nbase\nM 100644 :1 base.txt\ncommit refs/heads/feature\nmark :11\nauthor Dev2 <dev2@example.invalid> 2000 +0000\ncommitter Dev2 <dev2@example.invalid> 2000 +0000\ndata 5\nfeatX\nfrom :10\nM 100644 :2 feat.txt\ncommit refs/heads/main\nmark :12\nauthor Dev1 <dev1@example.invalid> 3000 +0000\ncommitter Dev1 <dev1@example.invalid> 3000 +0000\ndata 5\nmerge\nfrom :10\nmerge :11\nM 100644 :3 merge.txt\ntag v3.0\nfrom :12\ntagger Releaser <rel@example.invalid> 3001 +0000\ndata 12\nfinal merge\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import complex.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$SRC/out.fi\" >/dev/null\ngit checkout -q main\nprintf 'merge_txt=%s\\n' \"$(cat merge.txt | tr '\\n' '|')\"\nprintf 'parents=%s\\n' \"$(git log --pretty=format:'%P' -1 HEAD | wc -w | tr -d ' ')\"\nprintf 'v3_type=%s\\n' \"$(git cat-file -t refs/tags/v3.0 2>/dev/null || echo none)\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("merge_txt=MRG|")
expect(out).to_contain("parents=2")
expect(out).to_contain("v3_type=tag")
expect(out).to_contain("exit=0")
```

</details>

#### round-trips inline blobs identically to mark-referenced blobs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-roundtrip-inline.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-roundtrip-inline-git.XXXXXX)\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > inline_rt.fi <<'EOF'\ncommit refs/heads/main\nauthor Alice <alice@example.invalid> 5000 +0000\ncommitter Alice <alice@example.invalid> 5000 +0000\ndata 12\nadd inline\nM 100644 inline readme.txt\ndata 16\ninline-content!\n\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import inline_rt.fi >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi main\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$SRC/out.fi\" >/dev/null\ngit checkout -q main\nprintf 'readme=%s\\n' \"$(cat readme.txt | tr '\\n' '|')\"\n"
val out = _run_full_interop_script(script)
expect(out).to_contain("readme=inline-content!|")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
