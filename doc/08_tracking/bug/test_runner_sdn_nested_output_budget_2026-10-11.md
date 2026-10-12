# Test runner SDN nested output budget bypass

Status: open; source repair in development, native regression unrun.

The proposed `combined_test_run_sdn` serializer bounded file/block counts and
text totals but omitted nested artifact-path and block-modifier collection
counts. Large arrays of empty strings or non-text modifier values could pass
that preflight and allocate a large SDN value tree before the final encoded
size check. Counting text through `.bytes()` also copied oversized values
before rejecting them.

The repair must bound every nested collection and aggregate element count,
check text byte lengths before copying, and enforce a conservative encoded
size budget before constructing the output tree. Arithmetic must check the
remaining budget before addition. Rejection is an explicit serialization
error, never truncation or a successful partial result.

Required evidence: native fixtures for oversized nested empty collections,
oversized individual text, cumulative limits, and preservation of valid
resource/process and doctest fields. Source review alone does not close this
issue or satisfy the full SDN worker migration.

Affected source: `src/lib/nogc_sync_mut/test_runner/test_runner_output.spl`.
Related requirement: REQ-TRC-001; bounded operation: REQ-TRC-010.
