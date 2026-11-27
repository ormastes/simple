# Piped group stream owner V2 verification plan

Implementation owner: daemon lane. Final source reviewer: Astra daemon lead;
merge coordinator: root. The existing Sol worker owns the native broker boundary
and native fixtures; the lead owns the Simple service facade and transfer review.
No additional supervisor, registry, reader, ledger, or compiler repair is included.

| Requirement | Executable coverage | Acceptance |
|---|---|---|
| GSTREAM-01: explicit V2 profile preserves V1 constraints | `group_process_stream_protocol_v2_spec.spl` | Canonical round-trip and V1 arbitrary-argv rejection |
| GSTREAM-02: exact argv and transport identity | protocol spec; native fixture | Ordered byte digest and actual generation are request-bound |
| GSTREAM-03: launch-only authorization expiry | protocol spec; native fixture | Reject before child exec; do not shorten running lifetime |
| GSTREAM-04: complete owner transfer | `piped_process_owned_v2_spec.spl` | Full owner and all reference binding fields retained and checked |
| GSTREAM-05: stale or mismatched authority has no effects | owner spec; native fixture | No read/write/wait/signal/retire through another binding or old adapter |
| GSTREAM-06: failures retain cleanup authority | owner spec; native fixture | No-child proof is distinct; post-clone failures retain lease; failed publication retains real collected evidence |
| GSTREAM-07: exact lifecycle and byte purity | delegated Linux native fixture and compiled broker integration | Existing cgroup/pidfd owner proves tree empty; stdout contains child bytes only |
| GSTREAM-08: capacity release uses retained proof | host integration using existing GroupedReapReceiptV1 | Descriptor retirement does not acknowledge/release host capacity |

Native execution must use the ordinary linked runtime owners and a real writable
cgroup-v2 delegation. Unavailable capability must fail before helper fork. A
negative admission result is useful evidence but never qualifies positive tree
cleanup. Capture source hashes, command, affinity, timeout, output, exit status,
and binary hash for every actual run. New native checks are finite and limited to
this changed owner path; do not rerun the earlier passing V1 registry harness.

Full Simple protocol/facade tests, the compiled broker/service path, Windows
owned-stream implementation, core compiler/lib checks, and MCP native checks
remain separate gates. Mark unexecuted checks NOT_RUN, and keep the overall
status AWAITING_VERIFICATION until the required evidence actually exists.
