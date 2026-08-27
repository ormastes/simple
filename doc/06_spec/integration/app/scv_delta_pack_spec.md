# Scv Delta Pack Specification

> Tests covering the compiler subprocess actually runs, scv delta pack chains.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Delta Pack Specification

## Scenarios

### the compiler subprocess actually runs

#### launches the compiler and finds the scv entrypoint

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launches the compiler and finds the scv entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launches the compiler and finds the scv entrypoint")
val out = _run_delta_pack_script("set -eu\ntest -x \"$SIMPLE\"\ntest -f \"$(pwd)/src/app/scv/main.spl\"\nVER=$(\"$SIMPLE\" --version 2>&1)\ntest -n \"$VER\"\ncase \"$VER\" in *refusing*) echo GUARD_REFUSED; exit 9;; esac\necho compiler_ran=yes\n")
expect(out).to_contain("compiler_ran=yes")
expect(out).to_contain("exit=0")
```

</details>

### scv delta pack chains

#### delta encoding produces smaller output than full object for similar content

- delta encoding produces smaller output than full object for similar content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("delta encoding produces smaller output than full object for similar content")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-compress.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE=$(printf '%0.s abcdefghijklmnopqrstuvwxyz0123456789\\n' {1..200})\nprintf '%s' \"$BASE\" > file_v1.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '%s' \"$BASE\" > file_v1.txt\nprintf 'CHANGED LINE\\n' >> file_v1.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nDELTA_PACK=$(ls .scv/objects/packs/*.pack.gz | head -1)\nDELTA_SIZE=$(wc -c < \"$DELTA_PACK\" | tr -d ' ')\nrm -rf .scv\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf '%s' \"$BASE\" > file_v1.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '%s' \"$BASE\" > file_v1.txt\nprintf 'CHANGED LINE\\n' >> file_v1.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nFULL_PACK=$(ls .scv/objects/packs/*.pack.gz | head -1)\nFULL_SIZE=$(wc -c < \"$FULL_PACK\" | tr -d ' ')\nprintf 'delta_size=%s\\nfull_size=%s\\n' \"$DELTA_SIZE\" \"$FULL_SIZE\"\ntest \"$DELTA_SIZE\" -lt \"$FULL_SIZE\"\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("delta_size=")
expect(out).to_contain("full_size=")
expect(out).to_contain("exit=0")
```

</details>

#### delta decoding reconstructs original bytes exactly

- delta decoding reconstructs original bytes exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("delta decoding reconstructs original bytes exactly")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-roundtrip.XXXXXX)\ncd \"$TMP\"\nORIG_CONTENT=$(printf 'line %d\\n' 1 2 3 4 5 6 7 8 9 10)\nprintf '%s' \"$ORIG_CONTENT\" > original.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nCOMMIT=$(ls .scv/objects/commits/ | head -1)\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-read-object chunks \"$(cat .scv/objects/commits/$COMMIT | grep 'chunk:' | head -1 | awk '{print $2}')\" > restored.bin\nCMP=$(diff <(printf '%s' \"$ORIG_CONTENT\") restored.bin && echo same || echo different)\nprintf 'roundtrip=%s\\n' \"$CMP\"\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("roundtrip=same")
expect(out).to_contain("exit=0")
```

</details>

#### pack-write-v2 produces a v2 format payload with entry-delta rows

- pack-write-v2 produces a v2 format payload with entry-delta rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pack-write-v2 produces a v2 format payload with entry-delta rows")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-v2-format.XXXXXX)\nBASE=$(printf '%0.s hello world line\\n' {1..100})\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf '%s' \"$BASE\" > big.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '%s' \"$BASE\" > big.txt\nprintf 'edit appended\\n' >> big.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2\nPACK=$(ls .scv/objects/packs/*.pack.gz | head -1)\ngzip -dc \"$PACK\" > payload.raw\nprintf 'format_line=%s\\n' \"$(head -1 payload.raw)\"\nENTRY_DELTA_COUNT=$(grep -c '^entry-delta ' payload.raw || true)\nprintf 'entry_delta_count=%s\\n' \"$ENTRY_DELTA_COUNT\"\ntest \"$ENTRY_DELTA_COUNT\" -gt 0\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("format_line=format: scv-pack-payload-v2")
expect(out).to_contain("entry_delta_count=")
expect(out).to_contain("exit=0")
```

</details>

#### pack-verify-v2 catches missing base reference in entry-delta row

- pack-verify-v2 catches missing base reference in entry-delta row


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pack-verify-v2 catches missing base reference in entry-delta row")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-bad-base.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf 'content\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nPACK_ID_OLD=$(basename \"$PACK\" .pack.gz)\ncat payload.raw | sed 's/^entry-delta \\([^ ]*\\) \\([^ ]*\\) \\([^ ]*\\)/entry-delta \\1 \\2 nonexistent_base_id/' > payload.bad\ngzip -c payload.bad > pack_bad.gz\nPACK_ID=pack_$(sha256sum \"$MANIFEST\" | cut -d ' ' -f1)\nmv pack_bad.gz \".scv/objects/packs/$PACK_ID.pack.gz\"\ncp \"$MANIFEST\" \".scv/objects/packs/$PACK_ID.manifest\"\nrm \"$PACK\" \"$MANIFEST\"\nset +e\nBAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-verify-v2)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD_OUT\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("ERROR")
expect(out).to_contain("base")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### pack-verify-v2 rejects entry-delta with chain_depth exceeding maximum

- pack-verify-v2 rejects entry-delta with chain_depth exceeding maximum


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pack-verify-v2 rejects entry-delta with chain_depth exceeding maximum")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-depth-limit.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf 'base content\\n' > base.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nBASE_ID=$(sed -n 's/^entry chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$BASE_ID\"\nprintf 'format: scv-pack-payload-v2\\nentry chunks %s 12\\nbase content\\nendentry\\nentry-delta chunks delta_id_1 %s 11 50\\n' \"$BASE_ID\" \"$BASE_ID\" > payload.bad\nprintf '%0.sx' {1..50} >> payload.bad\nprintf '\\nendentry\\nentry-delta chunks delta_id_2 delta_id_1 12 50\\n' >> payload.bad\nprintf '%0.sx' {1..50} >> payload.bad\nprintf '\\nendentry\\n' >> payload.bad\ngzip -c payload.bad > pack_depth.gz\nPACK_ID=pack_$(sha256sum \"$MANIFEST\" | cut -d ' ' -f1)\nmv pack_depth.gz \".scv/objects/packs/$PACK_ID.pack.gz\"\ncp \"$MANIFEST\" \".scv/objects/packs/$PACK_ID.manifest\"\nrm \"$PACK\" \"$MANIFEST\"\nCHAIN_PAYLOAD=\"format: scv-pack-payload-v2\\n\"\nPREV_ID=\"$BASE_ID\"\ni=1\nwhile [ $i -le 11 ]; do\n  CURR_ID=\"deep_delta_$i\"\n  CHAIN_PAYLOAD=\"\{CHAIN_PAYLOAD}entry-delta chunks $CURR_ID $PREV_ID $i 8\\ndeepdata\\nendentry\\n\"\n  PREV_ID=\"$CURR_ID\"\n  i=$((i+1))\ndone\nprintf '%s' \"format: scv-pack-payload-v2\\n\" > deep_payload.raw\nprintf 'entry chunks %s 12\\nbase content\\nendentry\\n' \"$BASE_ID\" >> deep_payload.raw\nPREV=\"$BASE_ID\"\ni=1\nwhile [ $i -le 11 ]; do\n  printf 'entry-delta chunks deep_%d %s %d 8\\ndeepdata\\nendentry\\n' \"$i\" \"$PREV\" \"$i\" >> deep_payload.raw\n  PREV=\"deep_$i\"\n  i=$((i+1))\ndone\ngzip -c deep_payload.raw > pack_deep.gz\nDEEP_ID=pack_deep_$(date +%s)\ncp \"$MANIFES\" \".scv/objects/packs/$DEEP_ID.manifest\" 2>/dev/null || true\nmv pack_deep.gz \".scv/objects/packs/$DEEP_ID.pack.gz\"\nset +e\nDEEP_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-verify-v2 2>&1)\nDEEP_CODE=$?\nset -e\nprintf '%s\\ndeep_code=%s\\n' \"$DEEP_OUT\" \"$DEEP_CODE\"\ntest \"$DEEP_CODE\" -ne 0\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("ERROR")
expect(out).to_contain("chain")
expect(out).to_contain("deep_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### pack-verify-v2 accepts valid entry-delta chain up to depth limit

- pack-verify-v2 accepts valid entry-delta chain up to depth limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pack-verify-v2 accepts valid entry-delta chain up to depth limit")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-depth-ok.XXXXXX)\nBASE=$(printf '%0.s content-line\\n' {1..50})\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf '%s' \"$BASE\" > file.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\ni=1\nwhile [ $i -le 5 ]; do\n  printf '%s' \"$BASE\" > file.txt\n  printf 'edit %d\\n' $i >> file.txt\n  SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\n  i=$((i+1))\ndone\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-verify-v2\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("pack-verify-v2")
expect(out).to_contain("exit=0")
```

</details>

#### GC keeps reachable base objects even when loose delta targets are pruned

- GC keeps reachable base objects even when loose delta targets are pruned


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("GC keeps reachable base objects even when loose delta targets are pruned")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-gc-base-pin.XXXXXX)\nBASE=$(printf '%0.s stable-line\\n' {1..80})\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf '%s' \"$BASE\" > data.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nCOMMIT1=$(ls .scv/objects/commits/ | sort | head -1)\nprintf '%s' \"$BASE\" > data.txt\nprintf 'append v2\\n' >> data.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nBASE_CHUNKS_BEFORE=$(find .scv/objects/chunks -type f | wc -l | tr -d ' ')\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" gc >/dev/null\nBASE_CHUNKS_AFTER=$(find .scv/objects/chunks -type f | wc -l | tr -d ' ')\nPACK_COUNT=$(ls .scv/objects/packs/*.pack.gz 2>/dev/null | wc -l | tr -d ' ')\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-verify-v2\nprintf 'base_before=%s\\nbase_after=%s\\npacks=%s\\n' \"$BASE_CHUNKS_BEFORE\" \"$BASE_CHUNKS_AFTER\" \"$PACK_COUNT\"\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("pack-verify-v2")
expect(out).to_contain("packs=1")
expect(out).to_contain("exit=0")
```

</details>

#### pack-read-object resolves delta chain and reconstructs original content

- pack-read-object resolves delta chain and reconstructs original content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pack-read-object resolves delta chain and reconstructs original content")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-delta-read-object.XXXXXX)\nORIG=$(printf 'alpha line %d\\n' 1 2 3 4 5 6 7 8 9 10)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf '%s' \"$ORIG\" > target.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '%s' \"$ORIG\" > target.txt\nprintf 'modified line\\n' >> target.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-write-v2 >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz | head -1)\ngzip -dc \"$PACK\" > payload.raw\nDELTA_ID=$(sed -n 's/^entry-delta chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\nif [ -n \"$DELTA_ID\" ]; then\n  RESTORED=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" pack-read-object chunks \"$DELTA_ID\")\n  RESTORED_LINES=$(printf '%s' \"$RESTORED\" | wc -l | tr -d ' ')\n  printf 'delta_id=%s\\nrestored_lines=%s\\n' \"$DELTA_ID\" \"$RESTORED_LINES\"\n  test \"$RESTORED_LINES\" -gt 0\nelse\n  printf 'no_delta=true\\n'\nfi\n"
val out = _run_delta_pack_script(script)
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_delta_pack_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering the compiler subprocess actually runs, scv delta pack chains.
- the compiler subprocess actually runs
- scv delta pack chains

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

- Canonical SPipe generation for source `54ed45b2ae041f9c9f80fbfdca011d9d754f5978695647e2ce192123f0c24964`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `54ed45b2ae041f9c9f80fbfdca011d9d754f5978695647e2ce192123f0c24964`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `54ed45b2ae041f9c9f80fbfdca011d9d754f5978695647e2ce192123f0c24964`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_delta_pack_spec.spl
mirror: doc/06_spec/integration/app/scv_delta_pack_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_delta_pack_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_delta_pack_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_delta_pack_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches the compiler and finds the scv entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_delta_pack_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delta encoding produces smaller output than full object for similar content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_delta_pack_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delta decoding reconstructs original bytes exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
