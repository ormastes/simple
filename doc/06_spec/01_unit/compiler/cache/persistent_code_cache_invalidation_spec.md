# Persistent Code Cache Invalidation Specification

> Tests covering persistent code cache — source change invalidates, persistent code cache — every key axis invalidates, persistent code cache — sabotage falls back to cold.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Persistent Code Cache Invalidation Specification

## Scenarios

### persistent code cache — source change invalidates

#### a changed source MUST NOT reuse the entry stored for the old source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a changed source MUST NOT reuse the entry stored for the old source


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a changed source MUST NOT reuse the entry stored for the old source")
val root = fresh_root()
pcc_store(root, key_for(SRC_A), prepare(SRC_A))
val stale = pcc_load(root, key_for(SRC_SIG))
expect(stale.hit).to_be(false)
expect(stale.words.len()).to_be(0)
```

</details>

#### POSITIVE CONTROL: the unchanged source still hits on that same root

- POSITIVE CONTROL: the unchanged source still hits on that same root


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: the unchanged source still hits on that same root")
val root = fresh_root()
pcc_store(root, key_for(SRC_A), prepare(SRC_A))
val changed = pcc_load(root, key_for(SRC_SIG))
val same = pcc_load(root, key_for(SRC_A))
expect(changed.hit).to_be(false)
expect(same.hit).to_be(true)
expect(same.words.len()).to_be(prepare(SRC_A).len())
```

</details>

#### re-storing under the new source makes the new source hit too

- re-storing under the new source makes the new source hit too


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-storing under the new source makes the new source hit too")
val root = fresh_root()
pcc_store(root, key_for(SRC_A), prepare(SRC_A))
pcc_store(root, key_for(SRC_SIG), prepare(SRC_SIG))
expect(pcc_load(root, key_for(SRC_A)).hit).to_be(true)
expect(pcc_load(root, key_for(SRC_SIG)).hit).to_be(true)
```

</details>

### persistent code cache — every key axis invalidates

#### a different target triple misses while the original still hits

- a different target triple misses while the original still hits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a different target triple misses while the original still hits")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, with_triple(k, "aarch64-unknown-linux-gnu")).hit).to_be(false)
expect(pcc_load(root, k).hit).to_be(true)
```

</details>

#### a different security policy misses while the original still hits

- a different security policy misses while the original still hits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a different security policy misses while the original still hits")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, with_policy(k, "policy/hardened")).hit).to_be(false)
expect(pcc_load(root, k).hit).to_be(true)
```

</details>

#### a different aspect/instrumentation identity misses

- a different aspect/instrumentation identity misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a different aspect/instrumentation identity misses")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, with_aspects(k, "aspects/trace")).hit).to_be(false)
expect(pcc_load(root, k).hit).to_be(true)
```

</details>

#### a dependency SIGNATURE change invalidates, a body-only change does not

- a dependency SIGNATURE change invalidates, a body-only change does not


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a dependency SIGNATURE change invalidates, a body-only change does not")
val dep_sig_old = dependency_interface_fold(["dep/x=" + interface_digest_of_source("fn f() -> i64:\n    1\n")])
val dep_body = dependency_interface_fold(["dep/x=" + interface_digest_of_source("fn f() -> i64:\n    99\n")])
val dep_sig_new = dependency_interface_fold(["dep/x=" + interface_digest_of_source("fn f(y: i64) -> i64:\n    1\n")])
expect(dep_body).to_be(dep_sig_old)
expect(dep_sig_new != dep_sig_old).to_be(true)
val root = fresh_root()
val k = with_deps(key_for(SRC_A), dep_sig_old)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, with_deps(k, dep_sig_new)).hit).to_be(false)
expect(pcc_load(root, with_deps(k, dep_body)).hit).to_be(true)
```

</details>

#### eviction is honoured and re-store restores the hit

- eviction is honoured and re-store restores the hit


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eviction is honoured and re-store restores the hit")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, k).hit).to_be(true)
pcc_evict(root, k)
expect(pcc_load(root, k).hit).to_be(false)
pcc_store(root, k, prepare(SRC_A))
expect(pcc_load(root, k).hit).to_be(true)
```

</details>

### persistent code cache — sabotage falls back to cold

#### a truncated entry file misses instead of half-loading

- a truncated entry file misses instead of half-loading


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a truncated entry file misses instead of half-loading")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
val path = pcc_entry_path(root, pcc_key_digest(k))
rt_file_write_text(path, "SPCC1\nkey=" + pcc_key_digest(k) + "\nwords=5\n")
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.words.len()).to_be(0)
expect(load.reason).to_be("truncated")
```

</details>

#### a body corrupted under a valid checksum header misses

- a body corrupted under a valid checksum header misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a body corrupted under a valid checksum header misses")
val root = fresh_root()
val k = key_for(SRC_A)
pcc_store(root, k, prepare(SRC_A))
val path = pcc_entry_path(root, pcc_key_digest(k))
val good = rt_file_read_text(path)
rt_file_write_text(path, good.replace("body=", "body=7,"))
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.reason).to_be("checksum-mismatch")
```

</details>

#### a non-numeric body token misses instead of guessing

- a non-numeric body token misses instead of guessing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-numeric body token misses instead of guessing")
val root = fresh_root()
val k = pcc_key_new("unit/garbage", "h", "d")
pcc_store(root, k, [1, 2, 3])
val path = pcc_entry_path(root, pcc_key_digest(k))
rt_file_write_text(path, "SPCC1\nkey=" + pcc_key_digest(k) + "\nwords=3\nchecksum=deadbeef\nbody=1,x,3\n")
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.words.len()).to_be(0)
```

</details>

#### an empty entry file misses

- an empty entry file misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an empty entry file misses")
val root = fresh_root()
val k = pcc_key_new("unit/empty-file", "h", "d")
pcc_store(root, k, [1])
rt_file_write_text(pcc_entry_path(root, pcc_key_digest(k)), "")
expect(pcc_load(root, k).hit).to_be(false)
```

</details>

#### a foreign file with the wrong magic misses

- a foreign file with the wrong magic misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a foreign file with the wrong magic misses")
val root = fresh_root()
val k = pcc_key_new("unit/foreign", "h", "d")
pcc_store(root, k, [1])
rt_file_write_text(pcc_entry_path(root, pcc_key_digest(k)), "NOTSPCC\nkey=x\nwords=1\nchecksum=y\nbody=1\n")
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.reason).to_be("bad-magic")
```

</details>

#### an entry echoing a DIFFERENT key misses even at the right path

- an entry echoing a DIFFERENT key misses even at the right path


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an entry echoing a DIFFERENT key misses even at the right path")
val root = fresh_root()
val k = pcc_key_new("unit/echo", "h", "d")
pcc_store(root, k, [1, 2])
rt_file_write_text(pcc_entry_path(root, pcc_key_digest(k)), "SPCC1\nkey=0000\nwords=2\nchecksum=z\nbody=1,2\n")
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.reason).to_be("key-mismatch")
```

</details>

#### a word count that disagrees with the body misses

- a word count that disagrees with the body misses


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a word count that disagrees with the body misses")
val root = fresh_root()
val k = pcc_key_new("unit/count", "h", "d")
pcc_store(root, k, [1, 2, 3])
val path = pcc_entry_path(root, pcc_key_digest(k))
val good = rt_file_read_text(path)
rt_file_write_text(path, good.replace("words=3", "words=9"))
val load = pcc_load(root, k)
expect(load.hit).to_be(false)
expect(load.words.len()).to_be(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering persistent code cache — source change invalidates, persistent code cache — every key axis invalidates, persistent code cache — sabotage falls back to cold.
- persistent code cache — source change invalidates
- persistent code cache — every key axis invalidates
- persistent code cache — sabotage falls back to cold

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c51b7b36927d8075f00bd7814f6d3965858ff65b6818ccaaa1dc7879eb680b1d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c51b7b36927d8075f00bd7814f6d3965858ff65b6818ccaaa1dc7879eb680b1d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c51b7b36927d8075f00bd7814f6d3965858ff65b6818ccaaa1dc7879eb680b1d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a changed source MUST NOT reuse the entry stored for the old source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: the unchanged source still hits on that same root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/persistent_code_cache_invalidation_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-storing under the new source makes the new source hit too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
