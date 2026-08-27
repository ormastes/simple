# Flat Pool Codec Roundtrip Specification

> Tests covering flat pool codec primitives, flat pool codec fails closed on corruption, flat pool codec scalar primitives.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Pool Codec Roundtrip Specification

## Scenarios

### flat pool codec primitives

#### round-trips an i64 pool including negatives and zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips an i64 pool including negatives and zero
   - Expected: decoded.len() equals `original.len()`
   - Expected: decoded[i] equals `original[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips an i64 pool including negatives and zero")
val original = [0, 1, -1, 42, -99999, 2147483648]
val decoded = flat_pool_dec_i64(FlatPoolReader.new(flat_pool_enc_i64(original)))
expect(decoded.len()).to_equal(original.len())
var i = 0
while i < original.len():
    expect(decoded[i]).to_equal(original[i])
    i = i + 1
```

</details>

#### round-trips an empty pool as empty, not as one blank element

- round-trips an empty pool as empty, not as one blank element
   - Expected: decoded.len() equals `0`
   - Expected: decoded_text.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips an empty pool as empty, not as one blank element")
val decoded = flat_pool_dec_i64(FlatPoolReader.new(flat_pool_enc_i64([])))
expect(decoded.len()).to_equal(0)
val decoded_text = flat_pool_dec_text(FlatPoolReader.new(flat_pool_enc_text([])))
expect(decoded_text.len()).to_equal(0)
```

</details>

#### round-trips text containing newlines and backslashes

- round-trips text containing newlines and backslashes
   - Expected: decoded.len() equals `original.len()`
   - Expected: decoded[i] equals `original[i]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips text containing newlines and backslashes")
# Exactly what a Simple string literal or doc comment carries. Without
# escaping, the embedded newline would split one value into two lines
# and desynchronise every later read in the blob.
val original = ["", "plain", "with\nnewline", "back\\slash",
                "both\\\nmixed", "trailing\n", "\n", "\\"]
val decoded = flat_pool_dec_text(FlatPoolReader.new(flat_pool_enc_text(original)))
expect(decoded.len()).to_equal(original.len())
var i = 0
while i < original.len():
    expect(decoded[i]).to_equal(original[i])
    i = i + 1
```

</details>

#### round-trips nested i64 lists preserving inner empties

- round-trips nested i64 lists preserving inner empties
   - Expected: decoded.len() equals `4`
   - Expected: decoded[0].len() equals `3`
   - Expected: decoded[1].len() equals `0`
   - Expected: decoded[2][0] equals `0`
   - Expected: decoded[3][1] equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips nested i64 lists preserving inner empties")
val original = [[1, 2, 3], [], [0], [-5, 7]]
val decoded = flat_pool_dec_i64_list(FlatPoolReader.new(flat_pool_enc_i64_list(original)))
expect(decoded.len()).to_equal(4)
expect(decoded[0].len()).to_equal(3)
expect(decoded[1].len()).to_equal(0)
expect(decoded[2][0]).to_equal(0)
expect(decoded[3][1]).to_equal(7)
```

</details>

#### round-trips nested text lists with awkward payloads

- round-trips nested text lists with awkward payloads
   - Expected: decoded.len() equals `3`
   - Expected: decoded[0][1] equals `b\nc`
   - Expected: decoded[1].len() equals `0`
   - Expected: decoded[2].len() equals `1`
   - Expected: decoded[2][0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips nested text lists with awkward payloads")
val original = [["a", "b\nc"], [], [""]]
val decoded = flat_pool_dec_text_list(FlatPoolReader.new(flat_pool_enc_text_list(original)))
expect(decoded.len()).to_equal(3)
expect(decoded[0][1]).to_equal("b\nc")
expect(decoded[1].len()).to_equal(0)
expect(decoded[2].len()).to_equal(1)
expect(decoded[2][0]).to_equal("")
```

</details>

#### round-trips the triple-nested text pool (decl_type_param_constraints)

- round-trips the triple-nested text pool (decl_type_param_constraints)
   - Expected: decoded.len() equals `3`
   - Expected: decoded[0][0][1] equals `Eq`
   - Expected: decoded[0][1].len() equals `0`
   - Expected: decoded[1].len() equals `0`
   - Expected: decoded[2][0][0] equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips the triple-nested text pool (decl_type_param_constraints)")
val original = [[["Ord", "Eq"], []], [], [[""]]]
val decoded = flat_pool_dec_text_list_list(
    FlatPoolReader.new(flat_pool_enc_text_list_list(original)))
expect(decoded.len()).to_equal(3)
expect(decoded[0][0][1]).to_equal("Eq")
expect(decoded[0][1].len()).to_equal(0)
expect(decoded[1].len()).to_equal(0)
expect(decoded[2][0][0]).to_equal("")
```

</details>

#### round-trips a bool pool

- round-trips a bool pool
   - Expected: decoded.len() equals `3`
   - Expected: decoded[0] is true
   - Expected: decoded[1] is false
   - Expected: decoded[2] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips a bool pool")
val decoded = flat_pool_dec_bool(FlatPoolReader.new(flat_pool_enc_bool([true, false, true])))
expect(decoded.len()).to_equal(3)
expect(decoded[0]).to_equal(true)
expect(decoded[1]).to_equal(false)
expect(decoded[2]).to_equal(true)
```

</details>

#### preserves cursor position across consecutive pools in one blob

- preserves cursor position across consecutive pools in one blob
   - Expected: flat_pool_dec_i64(r).len() equals `2`
   - Expected: flat_pool_dec_text(r)[0] equals `x\ny`
   - Expected: flat_pool_dec_i64_list(r)[0][0] equals `9`
   - Expected: last[0] equals `7`
   - Expected: r.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves cursor position across consecutive pools in one blob")
# Real dumps concatenate ~154 pools into a single blob, so a decoder
# that over- or under-reads by one line corrupts every pool after it
# rather than failing where the defect is.
val blob = flat_pool_enc_i64([1, 2]) + flat_pool_enc_text(["x\ny"]) +
           flat_pool_enc_i64_list([[9]]) + flat_pool_enc_i64([7])
val r = FlatPoolReader.new(blob)
expect(flat_pool_dec_i64(r).len()).to_equal(2)
expect(flat_pool_dec_text(r)[0]).to_equal("x\ny")
expect(flat_pool_dec_i64_list(r)[0][0]).to_equal(9)
val last = flat_pool_dec_i64(r)
expect(last[0]).to_equal(7)
expect(r.ok).to_equal(true)
```

</details>

### flat pool codec fails closed on corruption

#### marks a truncated blob not-ok instead of hanging or short-reading

- marks a truncated blob not-ok instead of hanging or short-reading
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks a truncated blob not-ok instead of hanging or short-reading")
# A cache file cut off mid-write must become a MISS. The length header
# says 5 elements but only 2 lines remain.
val r = FlatPoolReader.new("5\n1\n2\n")
val _ = flat_pool_dec_i64(r)
expect(r.ok).to_equal(false)
```

</details>

#### rejects a negative length header

- rejects a negative length header
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects a negative length header")
val r = FlatPoolReader.new("-3\n1\n2\n")
val _ = flat_pool_dec_i64(r)
expect(r.ok).to_equal(false)
```

</details>

#### rejects an absurd length header without allocating for it

- rejects an absurd length header without allocating for it
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects an absurd length header without allocating for it")
# The guard is bounds-relative, so a huge count fails immediately
# rather than looping millions of times against a short blob.
val r = FlatPoolReader.new("999999999\n1\n")
val _ = flat_pool_dec_i64(r)
expect(r.ok).to_equal(false)
```

</details>

#### reading past the end of a blob sets not-ok

- reading past the end of a blob sets not-ok
   - Expected: first[0] equals `5`
   - Expected: r.ok is true
   - Expected: r.ok is true
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reading past the end of a blob sets not-ok")
# Every encoded line ends in "\n", so split() yields one trailing empty
# element. That element is legitimately readable; it is the read AFTER
# it that must trip the guard.
val r = FlatPoolReader.new("1\n5\n")
val first = flat_pool_dec_i64(r)
expect(first[0]).to_equal(5)
expect(r.ok).to_equal(true)
val _trailing = r.next()
expect(r.ok).to_equal(true)
val _past = r.next()
expect(r.ok).to_equal(false)
```

</details>

### flat pool codec scalar primitives

#### round-trips i64 scalars including negatives and zero

- round-trips i64 scalars including negatives and zero
   - Expected: flat_pool_dec_scalar_i64(r) equals `v`
   - Expected: r.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips i64 scalars including negatives and zero")
for v in [0, 1, -1, 7, -99999, 2147483648]:
    val r = FlatPoolReader.new(flat_pool_enc_scalar_i64(v))
    expect(flat_pool_dec_scalar_i64(r)).to_equal(v)
    expect(r.ok).to_equal(true)
```

</details>

#### round-trips bool scalars in both states

- round-trips bool scalars in both states
   - Expected: flat_pool_dec_scalar_bool(rt) is true
   - Expected: flat_pool_dec_scalar_bool(rf) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips bool scalars in both states")
val rt = FlatPoolReader.new(flat_pool_enc_scalar_bool(true))
expect(flat_pool_dec_scalar_bool(rt)).to_equal(true)
val rf = FlatPoolReader.new(flat_pool_enc_scalar_bool(false))
expect(flat_pool_dec_scalar_bool(rf)).to_equal(false)
```

</details>

#### round-trips text scalars containing newlines and backslashes

- round-trips text scalars containing newlines and backslashes
   - Expected: flat_pool_dec_scalar_text(r) equals `v`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips text scalars containing newlines and backslashes")
# PENDING_UNSAFE_REASON carries author-written prose straight from
# source, so an unescaped newline in it would desynchronise the blob.
for v in ["", "plain", "why\nnot", "back\\slash", "\n", "\\"]:
    val r = FlatPoolReader.new(flat_pool_enc_scalar_text(v))
    expect(flat_pool_dec_scalar_text(r)).to_equal(v)
```

</details>

#### keeps scalars and pools in step when interleaved in one blob

- keeps scalars and pools in step when interleaved in one blob
   - Expected: flat_pool_dec_text(r)[1] equals `b\nc`
   - Expected: flat_pool_dec_scalar_i64(r) equals `-3`
   - Expected: flat_pool_dec_scalar_bool(r) is true
   - Expected: flat_pool_dec_scalar_text(r) equals `re\\ason`
   - Expected: flat_pool_dec_i64(r)[1] equals `8`
   - Expected: r.ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps scalars and pools in step when interleaved in one blob")
# This is the real shape of flat_pending_pools_dump: [text] pools and
# i64/text scalars alternating. An off-by-one in either kind corrupts
# everything after it.
val blob = flat_pool_enc_text(["a", "b\nc"]) +
           flat_pool_enc_scalar_i64(-3) +
           flat_pool_enc_scalar_bool(true) +
           flat_pool_enc_scalar_text("re\\ason") +
           flat_pool_enc_i64([9, 8])
val r = FlatPoolReader.new(blob)
expect(flat_pool_dec_text(r)[1]).to_equal("b\nc")
expect(flat_pool_dec_scalar_i64(r)).to_equal(-3)
expect(flat_pool_dec_scalar_bool(r)).to_equal(true)
expect(flat_pool_dec_scalar_text(r)).to_equal("re\\ason")
expect(flat_pool_dec_i64(r)[1]).to_equal(8)
expect(r.ok).to_equal(true)
```

</details>

#### marks a blob truncated before a scalar not-ok

- marks a blob truncated before a scalar not-ok
   - Expected: r.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks a blob truncated before a scalar not-ok")
val r = FlatPoolReader.new("")
val _ = r.next()
val _2 = flat_pool_dec_scalar_i64(r)
expect(r.ok).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flat pool codec primitives, flat pool codec fails closed on corruption, flat pool codec scalar primitives.
- flat pool codec primitives
- flat pool codec fails closed on corruption
- flat pool codec scalar primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c908b7f01517e93b6681024b1668bbd6e366f8492018417f6116a6cf72f1ae3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c908b7f01517e93b6681024b1668bbd6e366f8492018417f6116a6cf72f1ae3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c908b7f01517e93b6681024b1668bbd6e366f8492018417f6116a6cf72f1ae3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips an i64 pool including negatives and zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips an empty pool as empty, not as one blank element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_pool_codec_roundtrip_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips text containing newlines and backslashes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
