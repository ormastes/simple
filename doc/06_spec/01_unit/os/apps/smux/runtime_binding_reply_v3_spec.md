# Strict runtime binding reply facts

Status: **AUTHORED_UNRUN**. Pure production codec imports. Synthetic reply bytes never enter a provider, host grant verifier, or stream owner.

Source: `test/01_unit/os/apps/smux/runtime_binding_reply_v3_spec.spl`.

1. Retain separate binding and common plan digests without asserting runtime success. Accept canonical bytes with at most one terminal newline and reject oversized input.
2. Reject ownership or release assertions without complete grant and adoption correlations. Partial helper grant identity is also rejected.
3. Fail closed on malformed or escalated reply facts: unsupported statuses, wrong types, additional authority fields, input, geometry, interactivity, or completion claims.

Binding digest hashes the canonical immutable binding request. Common request digest identifies the independently resolved Container output plan. Neither digest is a signed grant. Real helper ownership and host settlement require separate admitted evidence.
