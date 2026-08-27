# Udp Utils Facade Specification

> Tests covering gc_async_mut udp_utils facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Udp Utils Facade Specification

## Scenarios

### gc_async_mut udp_utils facade

#### re-exports UDP socket and datagram helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports UDP socket and datagram helpers
   - Expected: is_socket_bound(socket) equals `1`
   - Expected: get_socket_endpoint(socket) equals `127.0.0.1:9000`
   - Expected: is_socket_closed(close_socket(socket)) equals `1`
   - Expected: is_broadcast_enabled(tuned) equals `1`
   - Expected: get_multicast_ttl(tuned) equals `4`
   - Expected: is_in_multicast_group(joined, "224.0.0.1") equals `1`
   - Expected: validate_datagram(datagram) equals `1`
   - Expected: get_datagram_size(datagram) equals `13`
   - Expected: get_datagram_source(datagram) equals `127.0.0.1:9000`
   - Expected: get_datagram_destination(datagram) equals `224.0.0.1:9001`
   - Expected: compare_datagrams(datagram, create_reply_datagram(create_reply_datagram(datagram, "hello"), "hello")) equals `1`
   - Expected: is_valid_port(65535) equals `1`
   - Expected: is_well_known_port(80) equals `1`
   - Expected: is_registered_port(8080) equals `1`
   - Expected: is_dynamic_port(60000) equals `1`
   - Expected: is_ipv4_address("127.0.0.1") equals `1`
   - Expected: is_ipv6_address("::1") equals `1`
   - Expected: is_multicast_ipv4("224.0.0.1") equals `1`
   - Expected: is_broadcast_address("255.255.255.255") equals `1`
   - Expected: is_loopback_address("127.0.0.1") equals `1`
   - Expected: is_any_address("0.0.0.0") equals `1`
   - Expected: needs_fragmentation("small") equals `0`
   - Expected: calculate_fragment_count("abcdef", 2) equals `3`
   - Expected: calculate_fragment_count("abcdef", 0) equals `0`
   - Expected: create_fragment("abcdef", 2, 3) equals `cde`
   - Expected: create_fragment("abcdef", -1, 3) equals ``
   - Expected: create_fragment("abcdef", 4, 9) equals `ef`
   - Expected: get_max_payload_size() equals `65499`
   - Expected: can_send_datagram(socket, datagram) equals `1`
   - Expected: can_send_broadcast(enable_broadcast(socket), create_datagram("127.0.0.1", 9000, "255.255.255.255", 9001, "hello")) equals `1`
   - Expected: can_send_multicast(socket, datagram) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports UDP socket and datagram helpers")
val socket = bind_socket(create_udp_socket(), "127.0.0.1", 9000)
expect(is_socket_bound(socket)).to_equal(1)
expect(get_socket_endpoint(socket)).to_equal("127.0.0.1:9000")
expect(is_socket_closed(close_socket(socket))).to_equal(1)

val tuned = set_multicast_ttl(enable_broadcast(create_udp_socket_with_buffer_sizes(512, 512)), 4)
expect(is_broadcast_enabled(tuned)).to_equal(1)
expect(get_multicast_ttl(tuned)).to_equal(4)
val joined = join_multicast_group(socket, "224.0.0.1")
expect(is_in_multicast_group(joined, "224.0.0.1")).to_equal(1)

val datagram = create_datagram("127.0.0.1", 9000, "224.0.0.1", 9001, "hello")
expect(validate_datagram(datagram)).to_equal(1)
expect(get_datagram_size(datagram)).to_equal(13)
expect(get_datagram_source(datagram)).to_equal("127.0.0.1:9000")
expect(get_datagram_destination(datagram)).to_equal("224.0.0.1:9001")
expect(compare_datagrams(datagram, create_reply_datagram(create_reply_datagram(datagram, "hello"), "hello"))).to_equal(1)

expect(is_valid_port(65535)).to_equal(1)
expect(is_well_known_port(80)).to_equal(1)
expect(is_registered_port(8080)).to_equal(1)
expect(is_dynamic_port(60000)).to_equal(1)
expect(is_ipv4_address("127.0.0.1")).to_equal(1)
expect(is_ipv6_address("::1")).to_equal(1)
expect(is_multicast_ipv4("224.0.0.1")).to_equal(1)
expect(is_broadcast_address("255.255.255.255")).to_equal(1)
expect(is_loopback_address("127.0.0.1")).to_equal(1)
expect(is_any_address("0.0.0.0")).to_equal(1)

expect(needs_fragmentation("small")).to_equal(0)
expect(calculate_fragment_count("abcdef", 2)).to_equal(3)
expect(calculate_fragment_count("abcdef", 0)).to_equal(0)
expect(create_fragment("abcdef", 2, 3)).to_equal("cde")
expect(create_fragment("abcdef", -1, 3)).to_equal("")
expect(create_fragment("abcdef", 4, 9)).to_equal("ef")
expect(get_max_payload_size()).to_equal(65499)
expect(can_send_datagram(socket, datagram)).to_equal(1)
expect(can_send_broadcast(enable_broadcast(socket), create_datagram("127.0.0.1", 9000, "255.255.255.255", 9001, "hello"))).to_equal(1)
expect(can_send_multicast(socket, datagram)).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/udp_utils_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut udp_utils facade.
- gc_async_mut udp_utils facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `569aad5ff920f7bbd99f6cfd153b2ad15eaa707cd072a9af15557930913ede68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `569aad5ff920f7bbd99f6cfd153b2ad15eaa707cd072a9af15557930913ede68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `569aad5ff920f7bbd99f6cfd153b2ad15eaa707cd072a9af15557930913ede68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/udp_utils_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/udp_utils_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/udp_utils_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/udp_utils_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/udp_utils_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 25 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/udp_utils_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports UDP socket and datagram helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
