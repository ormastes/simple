# Scv Git Interop Specification

> <details>

<!-- sdn-diagram:id=scv_git_interop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_git_interop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_git_interop_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_git_interop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Git Interop Specification

## Scenarios

### scv git interchange

#### exports delete commands for paths removed since the parent commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-fast-export-delete-src.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-fast-export-delete-git.XXXXXX)\nprintf 'old\\n' > \"$SRC/a.txt\"\nprintf 'keep\\n' > \"$SRC/keep.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import first.fi main >/dev/null\nrm a.txt\nprintf 'new\\n' > keep.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import second.fi main\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$SRC/first.fi\" >/dev/null\ngit fast-import < \"$SRC/second.fi\" >/dev/null\ngit checkout -q main\ntest ! -e a.txt\nprintf 'keep=%s\\n' \"$(cat keep.txt | tr '\\n' '|')\"\nprintf 'delete_line=%s\\n' \"$(grep -c '^D a.txt$' \"$SRC/second.fi\")\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("export-git-fast-import second.fi")
expect(out).to_contain("deletes=1")
expect(out).to_contain("keep=new|")
expect(out).to_contain("delete_line=1")
expect(out).to_contain("exit=0")
```

</details>

#### imports fast-import modify commands as replacements and delete commands as removals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-delete.XXXXXX)\nprintf 'old\\n' > \"$TMP/a.txt\"\nprintf 'keep\\n' > \"$TMP/keep.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > update.fi <<'EOF'\nblob\nmark :1\ndata 4\nnew\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 7\nupdate\nM 100644 :1 keep.txt\nD a.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\nprintf 'keep=%s\\n' \"$(cat out/keep.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1 deleted=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("keep=new|")
expect(out).to_contain("exit=0")
```

</details>

#### imports fast-import blob payloads by byte count including multiline and empty files

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-byte-payload.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > update.fi <<'EOF'\nblob\nmark :1\ndata 11\nline1\nline2\nblob\nmark :2\ndata 0\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 13\nbyte payload\nM 100644 :1 multi.txt\nM 100644 :2 empty.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'multi=%s\\n' \"$(cat out/multi.txt | tr '\\n' '|')\"\nprintf 'empty_size=%s\\n' \"$(wc -c < out/empty.txt | tr -d ' ')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=2")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("multi=line1|line2|")
expect(out).to_contain("empty_size=0")
expect(out).to_contain("exit=0")
```

</details>

#### records chunk lists for large fast-import blob payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-large-blob.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nhead -c 2300 /dev/zero | tr '\\000' A > payload.bin\nprintf 'blob\\nmark :1\\ndata 2300\\n' > update.fi\ncat payload.bin >> update.fi\nprintf '\\ncommit refs/heads/main\\ncommitter scv <scv@example.invalid> 0 +0000\\ndata 5\\nlarge\\nM 100644 :1 big.txt\\n' >> update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nFILE=$(sed -n 's/.*|\\(file_[^|]*\\).*/\\1/p' .scv/meta/status_index.sdn | head -1)\nsed -n '1,20p' \".scv/objects/files/$FILE.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp payload.bin out/big.txt\nprintf 'export_size=%s\\n' \"$(wc -c < out/big.txt | tr -d ' ')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("chunks:")
expect(out).to_contain("export_size=2300")
expect(out).to_contain("exit=0")
```

</details>

#### imports executable fast-import file updates as byte content

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-exec.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > update.fi <<'EOF'\nblob\nmark :1\ndata 18\n#!/bin/sh\necho hi\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 5\nexec\nM 100755 :1 run.sh\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'run=%s\\n' \"$(cat out/run.sh | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("run=#!/bin/sh|echo hi|")
expect(out).to_contain("exit=0")
```

</details>

#### ignores command-looking text inside fast-import data payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-message-payload.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > update.fi <<'EOF'\nblob\nmark :1\ndata 5\nreal\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 22\nM 100644 :1 ghost.txt\nM 100644 :1 real.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import update.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/ghost.txt\nprintf 'real=%s\\n' \"$(cat out/real.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("real=real|")
expect(out).to_contain("exit=0")
```

</details>

#### imports delete-only fast-import commits as valid tree changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-delete-only.XXXXXX)\nprintf 'old\\n' > \"$TMP/a.txt\"\nprintf 'keep\\n' > \"$TMP/keep.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > delete.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 7\ndelete\nD a.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import delete.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\nprintf 'keep=%s\\n' \"$(cat out/keep.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=0 deleted=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("keep=keep|")
expect(out).to_contain("exit=0")
```

</details>

#### imports deleteall as a replacement tree reset

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-deleteall.XXXXXX)\nprintf 'old\\n' > \"$TMP/a.txt\"\nprintf 'keep\\n' > \"$TMP/keep.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > replace.fi <<'EOF'\nblob\nmark :1\ndata 4\nnew\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 8\nreplace\ndeleteall\nM 100644 :1 new.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import replace.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\ntest ! -e out/keep.txt\nprintf 'new=%s\\n' \"$(cat out/new.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1 deleted=2")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("new=new|")
expect(out).to_contain("exit=0")
```

</details>

#### imports fast-import rename commands as path moves

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-rename.XXXXXX)\nprintf 'old\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > rename.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 7\nrename\nR a.txt renamed.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import rename.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\ntest -e out/renamed.txt\nprintf 'renamed=%s\\n' \"$(cat out/renamed.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=0 deleted=0 renamed=1")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("renamed=old|")
expect(out).to_contain("exit=0")
```

</details>

#### imports fast-import copy commands as duplicated paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-copy.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > copy.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 5\ncopy\nC a.txt copy.txt\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import copy.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest -e out/a.txt\ntest -e out/copy.txt\nprintf 'a=%s\\ncopy=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\" \"$(cat out/copy.txt | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=0 deleted=0 renamed=0 copied=1")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("a=base|")
expect(out).to_contain("copy=base|")
expect(out).to_contain("exit=0")
```

</details>

#### rejects rename and copy commands whose source path is not tracked

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-missing-move-source.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > rename.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 7\nrename\nR missing.txt renamed.txt\nEOF\ncat > copy.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 5\ncopy\nC missing.txt copy.txt\nEOF\nset +e\nRENAME=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import rename.fi)\nRENAME_CODE=$?\nCOPY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import copy.fi)\nCOPY_CODE=$?\nset -e\nprintf '%s\\nrename_code=%s\\n%s\\ncopy_code=%s\\n' \"$RENAME\" \"$RENAME_CODE\" \"$COPY\" \"$COPY_CODE\"\ntest \"$RENAME_CODE\" -ne 0\ntest \"$COPY_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR missing rename source: missing.txt")
expect(out).to_contain("rename_code=1")
expect(out).to_contain("ERROR missing copy source: missing.txt")
expect(out).to_contain("copy_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects delete-only streams that do not remove any tracked path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-delete-missing.XXXXXX)\nprintf 'keep\\n' > \"$TMP/keep.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > delete.fi <<'EOF'\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 7\ndelete\nD missing.txt\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import delete.fi)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR fast-import stream has no file commands")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsupported fast-import file modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-bad-mode.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nmode\nM 120000 :1 link.txt\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR unsupported file mode: 120000")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate fast-import blob marks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-duplicate-mark.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-duplicate-mark-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > dup.fi <<'EOF'\nblob\nmark :1\ndata 4\none\nblob\nmark :1\ndata 4\ntwo\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\ndup\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import dup.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncp dup.fi \"$PUB/export.fi\"\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR duplicate blob mark: 1")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR duplicate fast-import blob mark: 1")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe fast-import commit refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-bad-ref.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-bad-ref-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/bad branch\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\ngood\nM 100644 :1 a.txt\ncommit refs/heads/bad branch\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 b.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR unsafe git branch: bad branch")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsafe fast-import git branch: bad branch")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### imports and exports quoted fast-import paths with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-space-path.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-fast-import-space-git.XXXXXX)\nprintf 'old\\n' > \"$TMP/space name.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ncat > import.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 5\nspace\nM 100644 :1 \"new name.txt\"\nD \"space name.txt\"\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import import.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e \"out/space name.txt\"\nprintf 'new=%s\\n' \"$(cat \"out/new name.txt\" | tr '\\n' '|')\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import export.fi main\nprintf 'quoted_m=%s\\n' \"$(grep -c '^M 100644 :[0-9][0-9]* \"new name.txt\"$' export.fi)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/export.fi\" >/dev/null\ngit checkout -q main\nprintf 'git_new=%s\\n' \"$(cat \"new name.txt\" | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1 deleted=1")
expect(out).to_contain("new=x|")
expect(out).to_contain("quoted_m=1")
expect(out).to_contain("git_new=x|")
expect(out).to_contain("exit=0")
```

</details>

#### imports and exports quoted fast-import paths with escaped characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-escaped-path.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-fast-import-escaped-git.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > import.fi <<'EOF'\nblob\nmark :1\ndata 5\nodd\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 8\nescaped\nM 100644 :1 \"quote\\\"slash\\\\name.txt\"\nEOF\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import import.fi\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nTARGET='out/quote\"slash\\name.txt'\nprintf 'target=%s\\n' \"$(cat \"$TARGET\" | tr '\\n' '|')\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import export.fi main\nprintf 'escaped_m=%s\\n' \"$(grep -F -c '\"quote\\\"slash\\\\name.txt\"' export.fi)\"\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$TMP/export.fi\" >/dev/null\ngit checkout -q main\nGIT_TARGET='quote\"slash\\name.txt'\nprintf 'git_target=%s\\n' \"$(cat \"$GIT_TARGET\" | tr '\\n' '|')\"\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("import-git-fast-import files=1")
expect(out).to_contain("target=odd|")
expect(out).to_contain("escaped_m=1")
expect(out).to_contain("git_target=odd|")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unquoted fast-import paths with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-unquoted-space.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > import.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 5\nspace\nM 100644 :1 bad name.txt\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import import.fi)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR unsupported file command")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects malformed quoted fast-import paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-bad-quote.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :1 \"unterminated.txt\nEOF\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_git_interop_script(script)
expect(out).to_contain("ERROR unsupported file command")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_git_interop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv git interchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
