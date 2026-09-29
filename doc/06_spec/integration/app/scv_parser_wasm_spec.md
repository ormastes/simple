# Scv Parser Wasm Specification

> Tests covering scv parser WASM registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Wasm Specification

## Scenarios

### scv parser WASM registry

#### installs and locks a local WASM grammar artifact

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- installs and locks a local WASM grammar artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("installs and locks a local WASM grammar artifact")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-install.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32-tree-sitter\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\nls .scv/parsers/*.wasm\nprintf 'magic=%s\\n' \"$(od -An -tx1 -N4 .scv/parsers/*.wasm | tr -d ' ')\"\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("parser-install foo tree-sitter-foo 1.0.0")
expect(out).to_contain("runtime=wasm")
expect(out).to_contain("abi=wasm32-tree-sitter")
expect(out).to_contain("hash=sha256_")
expect(out).to_contain("parser-verify checked=1")
expect(out).to_contain("parser|foo|tree-sitter-foo|1.0.0|wasm|wasm32-tree-sitter|sha256_")
expect(out).to_contain(".scv/parsers/sha256_")
expect(out).to_contain("magic=0061736d")
expect(out).to_contain("exit=0")
```

</details>

#### rejects corrupted locked parser artifacts

- rejects corrupted locked parser artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects corrupted locked parser artifacts")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-verify-reject.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nprintf '\\000asmchanged' > .scv/parsers/*.wasm\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR parser artifact hash mismatch: foo tree-sitter-foo")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects corrupted parser lock artifacts before parser-index use

- fsck rejects corrupted parser lock artifacts before parser-index use


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects corrupted parser lock artifacts before parser-index use")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-fsck-lock-artifact.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '\\000asmchanged' > .scv/parsers/*.wasm\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("parser artifact hash mismatch: foo tree-sitter-foo")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects parser lock entries whose artifact path leaves the parser cache

- rejects parser lock entries whose artifact path leaves the parser cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects parser lock entries whose artifact path leaves the parser cache")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-path-reject.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nHASH=$(sed -n 's/^parser|.*|\\(sha256_[^|]*\\)|.*/\\1/p' .scv/meta/parsers.sdn)\nprintf '\\000asm\\001\\000\\000\\000' > /tmp/scv-parser-outside.wasm\nprintf 'parser|foo|tree-sitter-foo|1.0.0|wasm|wasm32|%s|/tmp/scv-parser-outside.wasm\\n' \"$HASH\" > .scv/meta/parsers.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR unsafe parser artifact path: foo tree-sitter-foo")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe parser artifact hashes before path construction

- rejects unsafe parser artifact hashes before path construction


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe parser artifact hashes before path construction")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-hash-path-reject.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nprintf 'parser|foo|tree-sitter-foo|1.0.0|wasm|wasm32|../bad|.scv/parsers/../bad.wasm\\n' > .scv/meta/parsers.sdn\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify)\nVERIFY_CODE=$?\nset -e\nprintf '%s\\nverify_code=%s\\n' \"$BAD_VERIFY\" \"$VERIFY_CODE\"\ntest \"$VERIFY_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR unsafe parser artifact hash: foo tree-sitter-foo")
expect(out).to_contain("verify_code=1")
expect(out).to_contain("unsafe parser artifact hash: foo tree-sitter-foo")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects non-WASM parser artifacts

- rejects non-WASM parser artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects non-WASM parser artifacts")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-reject.XXXXXX)\ncd \"$TMP\"\nprintf 'not wasm' > bad.bin\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 bad.bin wasm32)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR parser artifact is not wasm")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate parser lock entries

- rejects duplicate parser lock entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects duplicate parser lock entries")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-dup-lock.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\ncat .scv/meta/parsers.sdn >> .scv/meta/parsers.sdn\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify)\nVERIFY_CODE=$?\nset -e\nprintf '%s\\nverify_code=%s\\n' \"$BAD_VERIFY\" \"$VERIFY_CODE\"\ntest \"$VERIFY_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR duplicate parser lock entry: foo tree-sitter-foo")
expect(out).to_contain("verify_code=1")
expect(out).to_contain("duplicate parser lock entry: foo tree-sitter-foo")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects parser lock entries with extra fields

- rejects parser lock entries with extra fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects parser lock entries with extra fields")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-extra-lock.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nsed 's/$/|extra/' .scv/meta/parsers.sdn > .scv/meta/parsers.bad\nmv .scv/meta/parsers.bad .scv/meta/parsers.sdn\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify)\nVERIFY_CODE=$?\nset -e\nprintf '%s\\nverify_code=%s\\n' \"$BAD_VERIFY\" \"$VERIFY_CODE\"\ntest \"$VERIFY_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR bad parser lock entry")
expect(out).to_contain("verify_code=1")
expect(out).to_contain("bad parser lock entry:")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### uses locked parser metadata for mapped language parse indexes

- uses locked parser metadata for mapped language parse indexes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses locked parser metadata for mapped language parse indexes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-locked-view.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo foo tree-sitter-foo 1.0.0 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nsed -n '1,8p' \".scv/objects/syntax/$ROOT.sdn\"\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("parser: tree-sitter-foo")
expect(out).to_contain("execution: fallback-line")
expect(out).to_contain("sample.foo|foo|sha256_")
expect(out).to_contain("|tree-sitter-foo|parsed_ok|")
expect(out).to_contain("grammar: tree-sitter-foo")
expect(out).to_contain("version: 1.0.0")
expect(out).to_contain("parser_hash: sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### rejects parse-gate use of corrupted locked parser artifacts

- rejects parse-gate use of corrupted locked parser artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects parse-gate use of corrupted locked parser artifacts")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-locked-corrupt.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo foo tree-sitter-foo 1.0.0 >/dev/null\nprintf '\\000asmchanged' > .scv/parsers/*.wasm\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("ERROR parser artifact hash mismatch: foo tree-sitter-foo")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### invalidates parser cache when the locked artifact hash changes

- invalidates parser cache when the locked artifact hash changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("invalidates parser cache when the locked artifact hash changes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-cache-artifact.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo foo tree-sitter-foo 1.0.0 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf '\\000asm\\001\\000\\000\\000changed' > parser2.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser2.wasm wasm32 >/dev/null\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ncase \"$SECOND\" in *'cache: reused'*) exit 7;; esac\nprintf '%s\\nroot1=%s\\nroot2=%s\\n' \"$SECOND\" \"$ROOT1\" \"$ROOT2\"\ntest \"$ROOT1\" != \"$ROOT2\"\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("parser: tree-sitter-foo")
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects parser-index roots whose locked artifact hash changed

- fsck rejects parser-index roots whose locked artifact hash changed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects parser-index roots whose locked artifact hash changed")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-fsck-hash.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'alpha\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm wasm32 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo foo tree-sitter-foo 1.0.0 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck >/dev/null\nprintf '\\000asm\\001\\000\\000\\000changed' > parser2.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser2.wasm wasm32 >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_wasm_script(script)
expect(out).to_contain("parser hash mismatch: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_parser_wasm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv parser WASM registry.
- scv parser WASM registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `0e571acab8953cab7c7ba9fa43837bcf778ee82fc7402a3df863db121abc9a8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e571acab8953cab7c7ba9fa43837bcf778ee82fc7402a3df863db121abc9a8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e571acab8953cab7c7ba9fa43837bcf778ee82fc7402a3df863db121abc9a8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_parser_wasm_spec.spl
mirror: doc/06_spec/integration/app/scv_parser_wasm_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_parser_wasm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_parser_wasm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_parser_wasm_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs and locks a local WASM grammar artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_wasm_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects corrupted locked parser artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_wasm_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects corrupted parser lock artifacts before parser-index use' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
