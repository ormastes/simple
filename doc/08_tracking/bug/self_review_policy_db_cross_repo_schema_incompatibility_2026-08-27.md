# Self-review policy DB cross-repository schema incompatibility

Status: claimed by `work/review/local-20260827-004-self-review-policy-adapter`

Pinned audit inputs:

- Spipe main: `d5eafa5d9015eb665aaa89135c08f41a7ff80934`
- Simple main: `f5a3471c56db09a49e1a0d25336b241578f7e21f`

Simple's pure policy owner accepts a four-field `spipe-self-review-policy-db/1`
header with no `record_type`, nested exact identities, Unix timestamps, and a
`grant/1` record. Spipe uses the same database schema name for a different
three-field header with `record_type`, flat subject identities, canonical UTC
timestamps, and `spipe-self-review-subject-policy/1`. Spipe also binds an exact
higher-model receipt, while Simple currently permits caller-authorized
`self_attested` evidence (`src/app/release/self_review_policy.spl:734-743`).

The mismatch is fail-closed today but makes the advertised cross-repository
contract unusable. The paired Spipe parser reproduced rejection of Simple's
documented header as unknown `authority` and `max_ttl_seconds` fields; Simple's
closed header at `src/app/release/self_review_policy.spl:400-413` necessarily
rejects Spipe's `record_type` field.

Ownership: `src/app/release/self_review_policy.spl` is the pure-Simple owner;
no Rust/runtime change is needed or allowed. Resolution requires consuming the
canonical Spipe v2 JSONL schema, rejecting both v1 wire shapes, preserving exact
TTL/authority/identity/hash-chain checks, and accepting only authenticated
broker-signed higher-model evidence. Integration is blocked on the paired
Spipe schema PR and external operator replacement of v1 policy bytes; silent
or automatic migration is forbidden.
