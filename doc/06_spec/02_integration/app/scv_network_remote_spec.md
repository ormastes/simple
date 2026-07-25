# Scv Network Remote Specification

> <details>

<!-- sdn-diagram:id=scv_network_remote_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_network_remote_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_network_remote_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_network_remote_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Network Remote Specification

## Scenarios

### scv network remote push with fsck-verified pack

<details>
<summary>Advanced: pushes a verified branch to a loopback HTTP remote</summary>

#### pushes a verified branch to a loopback HTTP remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-push-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-push-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nprintf 'push_done=%s\\n' \"$?\"\ntest -f \"$REMOTE_DIR/branches/main/manifest.sdn\"\nprintf 'manifest_exists=1\\n'\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push-verify \"$REMOTE_DIR\" main\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("network-push")
expect(out).to_contain("push_done=0")
expect(out).to_contain("manifest_exists=1")
expect(out).to_contain("fsck ok")
expect(out).to_contain("exit=0")
```

</details>


</details>

#### rejects network push when public_ready gate has not been set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-push-nogate-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-push-nogate-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR public_ready gate not set")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects network push when pack fsck verification fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-push-fsck-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-push-fsck-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nPACK=$(find .scv/packs -name '*.gz' 2>/dev/null | head -1)\nif [ -n \"$PACK\" ]; then printf 'corrupted' >> \"$PACK\"; fi\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

### scv network remote pull with pack verification

<details>
<summary>Advanced: pulls a verified pack from a loopback HTTP remote and checks fsck</summary>

#### pulls a verified pack from a loopback HTTP remote and checks fsck

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-pull-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-net-pull-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-pull-remote.XXXXXX)\nprintf 'hello\\n' > \"$SRC/hello.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\ncmp \"$SRC/hello.txt\" hello.txt\nprintf 'pulled_hello=%s\\n' \"$(cat hello.txt | tr '\\n' '|')\"\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("network-pull")
expect(out).to_contain("remote_commit=commit_")
expect(out).to_contain("OK checked=")
expect(out).to_contain("pulled_hello=hello|")
expect(out).to_contain("exit=0")
```

</details>


</details>

#### rejects a pull when the remote pack manifest hash is corrupted

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-pull-corrupt-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-net-pull-corrupt-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-pull-corrupt-remote.XXXXXX)\nprintf 'data\\n' > \"$SRC/data.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main >/dev/null\nsed -E '0,/sha256_[0-9a-f]+/s//sha256_bad/' \"$REMOTE_DIR/branches/main/manifest.sdn\" > \"$REMOTE_DIR/branches/main/manifest.tmp\"\nmv \"$REMOTE_DIR/branches/main/manifest.tmp\" \"$REMOTE_DIR/branches/main/manifest.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

### scv network remote CAS ref update

#### performs a successful compare-and-swap refs update

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-cas-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-cas-remote.XXXXXX)\nprintf 'v1\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nCOMMIT1=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE_DIR/refs.sdn\")\nprintf 'commit1=%s\\n' \"$COMMIT1\"\nprintf 'v2\\n' >> a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nCOMMIT2=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE_DIR/refs.sdn\")\nprintf 'commit2=%s\\n' \"$COMMIT2\"\ntest \"$COMMIT1\" != \"$COMMIT2\"\nCOUNT=$(grep -c '^main|' \"$REMOTE_DIR/refs.sdn\")\nprintf 'main_refs=%s\\n' \"$COUNT\"\ntest \"$COUNT\" = 1\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("commit1=commit_")
expect(out).to_contain("commit2=commit_")
expect(out).to_contain("main_refs=1")
expect(out).to_contain("exit=0")
```

</details>

#### returns a conflict error and does not advance refs when a concurrent push races ahead

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-cas-conflict-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-cas-conflict-remote.XXXXXX)\nprintf 'base\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main >/dev/null\nOLD_ETAG=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE_DIR/refs.sdn\")\nprintf 'raced\\n' >> \"$REMOTE_DIR/refs.sdn.tmp\"\ncp \"$REMOTE_DIR/refs.sdn\" \"$REMOTE_DIR/refs.sdn.bak\"\nprintf 'v2\\n' >> a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nprintf 'format: scv-remote-refs-v1\\nmain|commit_raced_ahead|/nowhere\\n' > \"$REMOTE_DIR/refs.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push-cas \"http://127.0.0.1\" \"$REMOTE_DIR\" main \"$OLD_ETAG\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("conflict: remote advanced, pull first")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

### scv network remote SSRF origin validation

#### rejects a refs response whose pack_url points to a different host

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nDST=$(mktemp -d /tmp/scv-net-ssrf-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-ssrf-remote.XXXXXX)\nmkdir -p \"$REMOTE_DIR/branches/main\"\nprintf 'format: scv-remote-refs-v1\\nmain|commit_abc123def456abc123def456abc123def456abc1|http://internal-corp/secret/pack.gz\\n' > \"$REMOTE_DIR/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR ssrf")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects a refs response whose pack_url redirects to an RFC1918 address

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nDST=$(mktemp -d /tmp/scv-net-ssrf-rfc1918-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-ssrf-rfc1918-remote.XXXXXX)\nmkdir -p \"$REMOTE_DIR/branches/main\"\nprintf 'format: scv-remote-refs-v1\\nmain|commit_abc123def456abc123def456abc123def456abc1|http://10.0.0.1/pack.gz\\n' > \"$REMOTE_DIR/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR ssrf")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

<details>
<summary>Advanced: accepts a pack_url that stays within the same loopback origin</summary>

#### accepts a pack_url that stays within the same loopback origin

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-ssrf-ok-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-net-ssrf-ok-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-ssrf-ok-remote.XXXXXX)\nprintf 'ok\\n' > \"$SRC/ok.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nprintf 'ssrf_ok=1\\n'\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ssrf_ok=1")
expect(out).to_contain("exit=0")
```

</details>


</details>

### scv network remote interrupted transfer resume and discard

#### resumes an interrupted chunked upload from the last committed chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-resume-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-resume-remote.XXXXXX)\nprintf 'chunk_data\\n' > \"$SRC/data.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main --chunk-bytes=1024\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push-verify \"$REMOTE_DIR\" main\nprintf 'resumed_ok=1\\n'\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("resumed_ok=1")
expect(out).to_contain("exit=0")
```

</details>

#### discards a partially downloaded pack when the download is interrupted before verification

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-discard-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-net-discard-dst.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-discard-remote.XXXXXX)\nprintf 'partial\\n' > \"$SRC/p.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main >/dev/null\nPACK_URL=$(awk -F'|' '/^main\\|/ {print $3}' \"$REMOTE_DIR/refs.sdn\" 2>/dev/null || printf '')\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull-simulate-interrupt \"http://127.0.0.1\" \"$REMOTE_DIR\" main 2>&1 || true\nTMP_COUNT=$(find .scv/tmp -name '*.partial' 2>/dev/null | wc -l)\nprintf 'partial_files=%s\\n' \"$TMP_COUNT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-pull-discard \"$REMOTE_DIR\" main\nAFTER_COUNT=$(find .scv/tmp -name '*.partial' 2>/dev/null | wc -l)\nprintf 'after_discard=%s\\n' \"$AFTER_COUNT\"\ntest \"$AFTER_COUNT\" = 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("after_discard=0")
expect(out).to_contain("exit=0")
```

</details>

### scv network remote public_ready gate enforcement

#### blocks network push when public_ready is absent even after snapshot and test-gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-gate-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-gate-remote.XXXXXX)\nprintf 'data\\n' > \"$SRC/f.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR public_ready gate not set")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### allows network push after all gates pass including public_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-gate-ok-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-gate-ok-remote.XXXXXX)\nprintf 'ready\\n' > \"$SRC/r.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nprintf 'push_allowed=1\\n'\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("push_allowed=1")
expect(out).to_contain("exit=0")
```

</details>

### scv network remote auth method configuration

#### configures Token auth and includes the Authorization header in push requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-auth-token-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-auth-token-remote.XXXXXX)\nprintf 'secure\\n' > \"$SRC/s.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-config set-auth token --header=Authorization --token=test_token_abc >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://127.0.0.1\" \"$REMOTE_DIR\" main\nprintf 'auth_push_done=1\\n'\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("auth_push_done=1")
expect(out).to_contain("exit=0")
```

</details>

<details>
<summary>Advanced: rejects an https base_url with tls_verify=false unless host is loopback</summary>

#### rejects an https base_url with tls_verify=false unless host is loopback

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-tls-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-tls-remote.XXXXXX)\nprintf 'data\\n' > \"$SRC/d.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-config set-tls-no-verify --base-url=https://public-host.example.com)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR tls_verify=false only permitted for loopback")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>


</details>

<details>
<summary>Advanced: rejects a non-https base_url for non-loopback remotes</summary>

#### rejects a non-https base_url for non-loopback remotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-net-scheme-src.XXXXXX)\nREMOTE_DIR=$(mktemp -d /tmp/scv-net-scheme-remote.XXXXXX)\nprintf 'data\\n' > \"$SRC/d.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" network-push \"http://public-host.example.com\" \"$REMOTE_DIR\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_net_remote_script(script)
expect(out).to_contain("ERROR https required for non-loopback remote")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_network_remote_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv network remote push with fsck-verified pack
- scv network remote pull with pack verification
- scv network remote CAS ref update
- scv network remote SSRF origin validation
- scv network remote interrupted transfer resume and discard
- scv network remote public_ready gate enforcement
- scv network remote auth method configuration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
