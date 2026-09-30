# Public native-build omits canonical source inventory authority

Status: isolated source correction; refreshed-producer runtime tests pending.

## Reproduction and diagnosis

Pure-Simple Linux producer
`250c2d7fc6106e4a3bf5e978b4fda5ed604ae3691197b149b2ea584813b694b4`, built
from `e4ef2826ff12006989244f97af52abf3e7a57f63`, compiles a real Git-admitted
one-file Hello fixture through HIR 1/1 and stores its HIR cache entry. It then
fails with `cold HIR receipt authority incomplete`, exit 1 after 1.290 seconds.
No executable is produced. The fixture has no test-tree filtering ambiguity.

Evidence: `/mnt/simple-bootstrap-6b2/phase2-hello-root-250c-20260930/` contains
the exact argv, sanitized environment, producer/runtime hashes, source, compile
log, process identity and terminal result. The existing exclusive-claim launcher
must not be rerun as if it were a fresh attempt.

The native-build closure's fresh snapshot path published the snapshot root,
revision, commit, tree and manifest digest. It omitted the separate canonical
`SIMPLE_SCV_SOURCE_INVENTORY_DIGEST`. That value was published only by the
compiler-entrypoint admission route. The snapshot manifest hashes selected
path/content/length rows; the canonical inventory digest also covers schema,
generation and semantic metadata. Substituting one for the other is invalid.

## Shared correction

`app.compiler_entrypoint.source_authority` owns preparation, validation and
environment publication. Both the normal compiler admission and public
native-build closure call it. It imports neither the compiler driver nor the
package-module index.

Fresh acquisition uses the existing event-refresh protocol, acquires the frozen
snapshot, and checks CURRENT against the refreshed digest and generation.
Manifest rows must match the content identity and byte length in the canonical
inventory. Cold inventory refresh includes both src and test as before; the
snapshot selection remains exactly the supplied source roots.

Inherited acquisition opens the existing snapshot and reads its immutable
canonical generation by the inherited digest. It validates the same checkout
owner, generation, manifest digest/count and content membership. It does not
replace an inherited binding with a newer CURRENT. Missing or mismatched fields
fail closed. Closure memo identity includes every authority field so changed
environment bindings cannot reuse an earlier validated memo.

Publication clears the previous authority record and writes the snapshot root
permission marker last. Any failed setter clears partial fields. Admission
publishes source authority only after its package-index checks complete. Failed
preparation clears old authority instead of inheriting a previous request.

Inherited validation reads bounded metadata and traverses canonical inventory
plus selected manifest rows once, O(N + M), using a row membership map. It adds
no source-tree scan, subprocess, retry, sleep, or package-index initialization.
Fresh refresh retains the existing journal/cursor algorithm and only performs
full discovery for explicitly requested cold initialization. Exact snapshot
selectors such as `src/app` and the entry filename are reduced to supported
`src`/`test` families only for event refresh. Other families fail with an honest
unsupported-scope diagnostic. Incremental refresh preserves nonselected family
membership using the existing event protocol; snapshot selection stays exact.

## Verification

`test/01_unit/app/compiler_entrypoint/source_authority_spec.spl` creates real
Git Hello fixtures using the SOSIX process facade. Positional and named source
selection cases assert exact frozen bytes, distinct published digest domains,
valid inherited authority after CURRENT advances, refusal of stale fresh
authority, absent digest, generation mismatch, corrupt manifest input, and cleared
fields after invalid publication. A separate canonical-data case rejects a
manifest whose digest matches its bytes but whose row is not admitted. Corrupt
metadata tests call the pure binding validator rather than modifying a sealed
snapshot on disk.

Working/staged direct-env audits and whitespace checks are source gates. Runtime
execution, public named/positional Hello, and HIR receipt publication require a
refreshed self-hosted producer. No full bootstrap retry, cache deletion, seed
fallback, fabricated environment digest, or admission PASS is part of this fix.
