# Storage Addr Specification

> Tests covering storage_addr.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Addr Specification

## Scenarios

### storage_addr

#### is_known_alias

#### recognizes the single-endpoint 'minio' alias

- recognizes the single-endpoint 'minio' alias
   - Expected: is_known_alias("minio") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes the single-endpoint 'minio' alias")
expect(is_known_alias("minio")).to_equal(true)
```

</details>

#### rejects any other name (no multi-alias store yet)

- rejects any other name (no multi-alias store yet)
   - Expected: is_known_alias("prod") is false
   - Expected: is_known_alias("") is false
   - Expected: is_known_alias("minioish") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects any other name (no multi-alias store yet)")
expect(is_known_alias("prod")).to_equal(false)
expect(is_known_alias("")).to_equal(false)
expect(is_known_alias("minioish")).to_equal(false)
```

</details>

#### parse_storage_addr — remote addressing rows

#### bare alias -> bucket-listing target (bucket=\

- bare alias -> bucket-listing target (bucket=\
   - Expected: a.valid is true
   - Expected: a.is_remote is true
   - Expected: a.alias equals `minio`
   - Expected: a.bucket equals ``
   - Expected: a.key equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare alias -> bucket-listing target (bucket=\")
val a = parse_storage_addr("minio")
expect(a.valid).to_equal(true)
expect(a.is_remote).to_equal(true)
expect(a.alias).to_equal("minio")
expect(a.bucket).to_equal("")
expect(a.key).to_equal("")
```

</details>

#### alias/bucket -> object-listing target (key=\

- alias/bucket -> object-listing target (key=\
   - Expected: a.is_remote is true
   - Expected: a.alias equals `minio`
   - Expected: a.bucket equals `firmware-images`
   - Expected: a.key equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alias/bucket -> object-listing target (key=\")
val a = parse_storage_addr("minio/firmware-images")
expect(a.is_remote).to_equal(true)
expect(a.alias).to_equal("minio")
expect(a.bucket).to_equal("firmware-images")
expect(a.key).to_equal("")
```

</details>

#### alias/bucket/ (trailing slash) -> bucket set, key=\

- alias/bucket/ (trailing slash) -> bucket set, key=\
   - Expected: a.is_remote is true
   - Expected: a.bucket equals `firmware-images`
   - Expected: a.key equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alias/bucket/ (trailing slash) -> bucket set, key=\")
val a = parse_storage_addr("minio/firmware-images/")
expect(a.is_remote).to_equal(true)
expect(a.bucket).to_equal("firmware-images")
expect(a.key).to_equal("")
```

</details>

#### alias/bucket/key -> full object target

- alias/bucket/key -> full object target
   - Expected: a.is_remote is true
   - Expected: a.alias equals `minio`
   - Expected: a.bucket equals `firmware-images`
   - Expected: a.key equals `zynq/v1/fw.bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("alias/bucket/key -> full object target")
val a = parse_storage_addr("minio/firmware-images/zynq/v1/fw.bin")
expect(a.is_remote).to_equal(true)
expect(a.alias).to_equal("minio")
expect(a.bucket).to_equal("firmware-images")
expect(a.key).to_equal("zynq/v1/fw.bin")
```

</details>

#### key preserves every internal '/' verbatim (S3 pseudo-dirs, not a second split point)

- key preserves every internal '/' verbatim (S3 pseudo-dirs, not a second split point)
   - Expected: a.bucket equals `bucket`
   - Expected: a.key equals `a/b/c/d.bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("key preserves every internal '/' verbatim (S3 pseudo-dirs, not a second split point)")
val a = parse_storage_addr("minio/bucket/a/b/c/d.bin")
expect(a.bucket).to_equal("bucket")
expect(a.key).to_equal("a/b/c/d.bin")
```

</details>

#### parse_storage_addr — local paths

#### empty string is invalid

- empty string is invalid
   - Expected: a.valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string is invalid")
val a = parse_storage_addr("")
expect(a.valid).to_equal(false)
```

</details>

#### absolute path is local (first segment is empty, not an alias)

- absolute path is local (first segment is empty, not an alias)
   - Expected: a.valid is true
   - Expected: a.is_remote is false
   - Expected: a.local_path equals `/tmp/file.bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("absolute path is local (first segment is empty, not an alias)")
val a = parse_storage_addr("/tmp/file.bin")
expect(a.valid).to_equal(true)
expect(a.is_remote).to_equal(false)
expect(a.local_path).to_equal("/tmp/file.bin")
```

</details>

#### dotted relative path is local

- dotted relative path is local
   - Expected: a.is_remote is false
   - Expected: a.local_path equals `./local/file.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dotted relative path is local")
val a = parse_storage_addr("./local/file.txt")
expect(a.is_remote).to_equal(false)
expect(a.local_path).to_equal("./local/file.txt")
```

</details>

#### bare relative path with no alias-shaped prefix is local

- bare relative path with no alias-shaped prefix is local
   - Expected: a.is_remote is false
   - Expected: a.local_path equals `relative/path/file.bin`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bare relative path with no alias-shaped prefix is local")
val a = parse_storage_addr("relative/path/file.bin")
expect(a.is_remote).to_equal(false)
expect(a.local_path).to_equal("relative/path/file.bin")
```

</details>

#### no-slash filename is local

- no-slash filename is local
   - Expected: a.is_remote is false
   - Expected: a.local_path equals `myfile.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-slash filename is local")
val a = parse_storage_addr("myfile.spl")
expect(a.is_remote).to_equal(false)
expect(a.local_path).to_equal("myfile.spl")
```

</details>

#### unregistered alias-shaped prefix falls through to local (mirrors mc's own alias-typo behavior)

- unregistered alias-shaped prefix falls through to local (mirrors mc's own alias-typo behavior)
   - Expected: a.is_remote is false
   - Expected: a.local_path equals `otheralias/bucket/key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unregistered alias-shaped prefix falls through to local (mirrors mc's own alias-typo behavior)")
val a = parse_storage_addr("otheralias/bucket/key")
expect(a.is_remote).to_equal(false)
expect(a.local_path).to_equal("otheralias/bucket/key")
```

</details>

#### infer_cp_direction

#### local SRC + remote DST -> upload

- local SRC + remote DST -> upload
   - Expected: infer_cp_direction(src, dst) equals `upload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local SRC + remote DST -> upload")
val src = parse_storage_addr("/tmp/in.bin")
val dst = parse_storage_addr("minio/bucket/key.bin")
expect(infer_cp_direction(src, dst)).to_equal("upload")
```

</details>

#### remote SRC + local DST -> download

- remote SRC + local DST -> download
   - Expected: infer_cp_direction(src, dst) equals `download`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remote SRC + local DST -> download")
val src = parse_storage_addr("minio/bucket/key.bin")
val dst = parse_storage_addr("/tmp/out.bin")
expect(infer_cp_direction(src, dst)).to_equal("download")
```

</details>

#### remote SRC + remote DST -> error_remote_remote

- remote SRC + remote DST -> error_remote_remote
   - Expected: infer_cp_direction(src, dst) equals `error_remote_remote`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remote SRC + remote DST -> error_remote_remote")
val src = parse_storage_addr("minio/bucket/a.bin")
val dst = parse_storage_addr("minio/bucket/b.bin")
expect(infer_cp_direction(src, dst)).to_equal("error_remote_remote")
```

</details>

#### local SRC + local DST -> error_local_local

- local SRC + local DST -> error_local_local
   - Expected: infer_cp_direction(src, dst) equals `error_local_local`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local SRC + local DST -> error_local_local")
val src = parse_storage_addr("/tmp/a.bin")
val dst = parse_storage_addr("/tmp/b.bin")
expect(infer_cp_direction(src, dst)).to_equal("error_local_local")
```

</details>

#### resolve_alias_config — offline-safe branches only

#### unknown alias fails before touching any config/file/network

- unknown alias fails before touching any config/file/network
   - Expected: ok is false
   - Expected: err contains `unknown alias`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown alias fails before touching any config/file/network")
val (ok, _cfg, err) = resolve_alias_config("prod")
expect(ok).to_equal(false)
expect(err.contains("unknown alias")).to_equal(true)
```

</details>

#### empty alias is rejected

- empty alias is rejected
   - Expected: ok is false
   - Expected: err contains `empty alias`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty alias is rejected")
val (ok, _cfg, err) = resolve_alias_config("")
expect(ok).to_equal(false)
expect(err.contains("empty alias")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/storage_addr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering storage_addr.
- storage_addr

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `c003470599f4ef695de3b9861c4283f0117d0f9cef920d0dbbd82474869f9dd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c003470599f4ef695de3b9861c4283f0117d0f9cef920d0dbbd82474869f9dd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c003470599f4ef695de3b9861c4283f0117d0f9cef920d0dbbd82474869f9dd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/devhub/storage_addr_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/storage_addr_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/storage_addr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/storage_addr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/storage_addr_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'recognizes the single-endpoint 'minio' alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/storage_addr_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects any other name (no multi-alias store yet)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/storage_addr_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bare alias -> bucket-listing target (bucket=\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
