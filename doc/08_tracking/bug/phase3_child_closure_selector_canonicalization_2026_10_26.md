# Phase3 child closure selector canonicalization

Source backport: release/1.0.0 PR4855,
`0713822f67efb88c5b5ddcf8d7caf0de3dc367b0`. The parent signs canonical relative
source selectors, while the target's parse-shard consumer compares the supplied
physical selector spellings directly with those signed roots. Equivalent
checkout/snapshot absolute selectors can therefore fail strict request identity.

The donor changes a native-worker admission leaf introduced by broader
`66d783d31f2`, which is absent on this target. Importing that six-file preclosed
worker feature is unnecessary. Instead apply the identical existing canonical
selector owner to the target's actual inline `parse_shard_main.spl` admission
before its strict request reader. Parent/child use the same helper; source,
snapshot, inventory, producer hash, generation and request-digest checks remain.
Foreign/traversal/unauthenticated generated selectors fail closed. Root order
and duplicates remain exact; no request bytes, policy defaults or source epoch
are rewritten. No new worker route, gate bypass or whole-file donor overwrite.

The original three semantic selector/request-identity scenarios are retained
byte-identical: relative/checkout/snapshot parity; invalid roots; ordered
duplicates and strict request mismatch. Donor PR reports3/3 retained-gen13,
canonical3GiB/120s, exit0/quiescent1, peak440096KiB. Exact portable producer/
runtime/tool receipts are not available in this checkout; these historical
results are attributed donor evidence, not independently recertified or current
execution. Current specs, native end-to-end child admission, compiler/MCP checks
and performance remain UNRUN without a qualified general runner. No jobs or
live frozen83be/cache/build changes. Independent exact source review required.
