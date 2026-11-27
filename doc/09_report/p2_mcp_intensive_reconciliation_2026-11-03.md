# MCP intensive failure contract reconciliation

Bug: `app_mcp_intensive_spec_is_84s_not_a_hang_eight_real_failures_2026-08-10`.
Claim: `p2-mcp-intensive-20261103`, admitted 2026-11-03T08:12:33Z.
Inspected fetched release head: `524e65382b2`.

The original eight-failure report is not a current reproduction. Current
intensive assertions use `.?` followed by
`!= nil`, matching the documented payload-or-nil contract and the Pure
Simple interpreter's actual `EXPR_EXISTS_CHECK` owner. Changing that owner
to return bool would break binding/coalescing semantics.

Current source-mode `tools/call` reaches `dispatch_tool` and then
`make_tool_error`: unknown names yield `result.isError=true`, structured code
`-32601`, the rejected name, and no protocol `error`. Missing names use
`-32602`. Historical ancestor `f1b6a04b044` records a prior 35/35 verdict and
message-capitalization fix for an older facade. Current source and assertions
agree on capitalization. That commit's verdict is not reused as current PASS.

Current intensive groups have `only-compiled` tags. Their filtered interpreter
inventory cannot be substituted for the original full inventory. Existing
tests and tags remain intact. The new focused file has no suppression tags.

Nine authored scenarios in `intensive_failure_contract_spec.spl` cover the
six reported dictionary shapes with payload assertions, real unknown-tool
dispatch, falsy/empty dictionary values, and tool/protocol/success envelope
separation. Existing direct-dispatch regression coverage remains intact.
No production MCP or compiler change was made without a demonstrated defect.

Behavioral status: **TEST_BLOCKED**, zero executed cases; no qualified
self-hosted full CLI exists on this host. No ordinary Rust-seed fallback was
used. Required resume: focused tests, full intensive compiled inventory,
stdio integration, core compiler/library/MCP checks, and MCP native/NFR smoke
with actual test counts and producer/source/runtime identities.

Startup, lazy family imports, hot dispatch, cached tool listing, cache
invalidation, startup/latency/RSS targets are unchanged. No measured NFR PASS
is claimed. This is a draft evidence/coverage candidate, not bug closure.
