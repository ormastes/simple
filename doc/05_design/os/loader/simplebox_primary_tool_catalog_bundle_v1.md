# Simplebox primary-tool catalog bundle v1

Status: deterministic signed-candidate planning implemented; runtime unverified.

The only currently concrete primary-tool payload in this lane is
`/bin/simplebox`. Its eight command paths (`echo`, `true`, `false`, `pwd`,
`seq`, `cat`, `head`, and `wc`) are exact catalog aliases, not separate
artifacts. The planner therefore accepts exactly one record, freezes the
canonical alias vector and target, and rejects missing, extra, cross-target, or
identity-drifted records. This is comfortably below the catalog ceiling of 16
records per target and avoids eight duplicate manifests and payload copies.

Planning is intentionally shape-only. A signature-looking envelope does not
become authentication evidence. Only the package-private population path may
consume an accepted plan, and it delegates to
`installed_artifact_catalog_populate_from_boot_policy_v1`, which initializes
the authenticated trust owner, verifies Ed25519 over the canonical manifest
signing bytes and caller-supplied digest binding, verifies the trust-root hash,
and only then starts the irreversible catalog transaction. This lane does not
hash filesystem bytes or bind a build-produced expected digest; that remains a
required later image/launch transaction.

The plan is deterministic because its sole required canonical-path vector is
`[/bin/simplebox]` and its sole record retains the frozen alias order. The
consumer repeats every exact invariant, so mutation of the public value between
planning and population fails closed. Runtime launch authority, filesystem
handle hashing/promotion, and payload construction remain separate owners.
