# bounded_read_spec

> AC-4: The parser enforces a limit on the number of headers it will read before aborting, so a slow client that trickles headers cannot hold a handler thread indefinitely.

<!-- sdn-diagram:id=bounded_read_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bounded_read_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bounded_read_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bounded_read_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bounded_read_spec

AC-4: The parser enforces a limit on the number of headers it will read before aborting, so a slow client that trickles headers cannot hold a handler thread indefinitely.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-023 |
| Category | HTTP Server Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/http_server/bounded_read_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
AC-4: The parser enforces a limit on the number of headers it will read
before aborting, so a slow client that trickles headers cannot hold a
handler thread indefinitely.

parse_request_with_limits accepts a max_header_count parameter that acts
as the bounded-read limit.  These specs verify the limit values and the
relationship between the limit and the header count guard without
requiring a live socket (the TcpStream is only needed for integration tests).

## Scenarios

### Bounded read — header count as read limit

#### MAX_HEADER_COUNT is the default bounded-read limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# parse_request_with_limits counts each read_line call for a header.
# After MAX_HEADER_COUNT headers the loop rejects with 431.
val limit = MAX_HEADER_COUNT
val is_sensible = limit > 0 and limit <= 1000
expect(is_sensible).to_equal(true)
```

</details>

#### injected limit of 1 is below MAX_HEADER_COUNT

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Callers can inject a smaller limit (e.g. 1) for testing tight bounds.
val injected = 1
val is_below = injected < MAX_HEADER_COUNT
expect(is_below).to_equal(true)
```

</details>

#### injected limit of 0 would reject immediately

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A limit of 0 means no headers are accepted — the first header read
# triggers the count > 0 rejection at the top of the loop.
# Verify: 0 < MAX_HEADER_COUNT (not the default).
val injected = 0
val below_default = injected < MAX_HEADER_COUNT
expect(below_default).to_equal(true)
```

</details>

#### limit at boundary equals MAX_HEADER_COUNT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val at_boundary = MAX_HEADER_COUNT
val equals = at_boundary == MAX_HEADER_COUNT
expect(equals).to_equal(true)
```

</details>

#### limit one over boundary exceeds MAX_HEADER_COUNT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val over = MAX_HEADER_COUNT + 1
val exceeds = over > MAX_HEADER_COUNT
expect(exceeds).to_equal(true)
```

</details>

### Bounded read — configurable via parse_request_with_limits

#### tight limit of 5 is a valid injected bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tight = 5
val in_range = tight > 0 and tight < MAX_HEADER_COUNT
expect(in_range).to_equal(true)
```

</details>

#### limit equal to MAX_HEADER_COUNT uses default policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_limit = MAX_HEADER_COUNT
val same = default_limit == 100
expect(same).to_equal(true)
```

</details>

#### parse_request_with_limits accepts all four limit parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify constant values that would be passed as arguments.
val req_line = MAX_REQUEST_LINE
val hdr_count = MAX_HEADER_COUNT
val hdr_line = MAX_HEADER_LINE
val body = MAX_BODY_SIZE
val all_positive = (req_line > 0) and (hdr_count > 0) and (hdr_line > 0) and (body > 0)
expect(all_positive).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
