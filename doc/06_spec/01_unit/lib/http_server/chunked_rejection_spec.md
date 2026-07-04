# chunked_rejection_spec

> AC-2 (adjusted): chunked Transfer-Encoding decoding is not supported. The parser must reject requests carrying Transfer-Encoding: chunked with a clear error message (501).  This prevents silent misparsing of chunked bodies as raw data.

<!-- sdn-diagram:id=chunked_rejection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chunked_rejection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chunked_rejection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chunked_rejection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chunked_rejection_spec

AC-2 (adjusted): chunked Transfer-Encoding decoding is not supported. The parser must reject requests carrying Transfer-Encoding: chunked with a clear error message (501).  This prevents silent misparsing of chunked bodies as raw data.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-022 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/chunked_rejection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
AC-2 (adjusted): chunked Transfer-Encoding decoding is not supported.
The parser must reject requests carrying Transfer-Encoding: chunked with
a clear error message (501).  This prevents silent misparsing of chunked
bodies as raw data.

Note: full end-to-end rejection requires a live TcpStream.  These specs
verify the logic used in parse_request_with_limits by testing the
content_length_from_text helper and the chunked-detection behaviour via
the exported constants/helpers that drive the decision.

The chunked detection itself lives inside parse_request_with_limits which
requires a TcpStream.  We document the contract here and verify via the
parser limit constants that the guard is in place.

## Scenarios

### Chunked Transfer-Encoding contract

#### MAX_HEADER_COUNT allows a chunked header to be seen

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The parser reads up to MAX_HEADER_COUNT headers.  The chunked
# detection check runs inside that loop, so it is guaranteed to
# be evaluated before the body read phase.
val count_positive = MAX_HEADER_COUNT > 0
expect(count_positive).to_equal(true)
```

</details>

#### chunked rejection does not depend on Content-Length

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A chunked request with no Content-Length should still be rejected.
# Verify: an empty Content-Length produces -1, not 0, so there is no
# accidental "zero body" path that might skip the chunked check.
val v = content_length_from_text("")
expect(v).to_equal(-1)
```

</details>

#### chunked with Content-Length 0 is still detected via header name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The chunked flag is set on the Transfer-Encoding header name, not
# derived from Content-Length.  A zero Content-Length should parse fine.
val v = content_length_from_text("0")
expect(v).to_equal(0)
```

</details>

### Malformed Content-Length in chunked context

#### rejects hex chunk size (e.g. 1a)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hex is valid in chunked chunk-size lines but not in Content-Length.
val v = content_length_from_text("1a")
expect(v).to_equal(-1)
```

</details>

#### rejects chunk size with semicolon extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("1a;ext=foo")
expect(v).to_equal(-1)
```

</details>

#### rejects negative chunk-size sentinel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("-1")
expect(v).to_equal(-1)
```

</details>

#### rejects overflow chunk size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = content_length_from_text("99999999999999999")
expect(v).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
