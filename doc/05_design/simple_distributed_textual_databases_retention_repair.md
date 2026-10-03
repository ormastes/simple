# Reproduction protection repair

This additive local owner supports selected REQ019/REQ032 retention honesty.
It does not change selected requirements or establish remote deletion authority.
Source and regression scenarios require an admitted runtime; execution is
UNEXECUTED. Protected publication, large-catalog retention and performance
qualification remain separate open work.

`db_retention_repair_reproduction(root, parent, expected, now_day)` returns
`Result<DbRetentionProtection,text>`. The existing root SJ lease covers catalog
reopen, exact HEAD comparison, actual CAS reads, strict planning and publication.
There is no restoration boolean, caller closure receipt or production signing.

The owner collects all `reproduction_incomplete` roots, reads each nondeleted
catalog object through the existing digest-verifying external CAS owner, and
traverses every actual dependency edge. Every reachable node must be registered,
nondeleted and unrestricted in both catalog and actual SCRE1 content. Cycles and
shared descendants are visited once. Catalog presence alone proves nothing.
Each marker root must already have a matching permanent `reproduction` pin;
orphan markers fail with `SCVDB_PIN_REPAIR_REQUIRED`, without inventing a pin.
Ordinary strict retention planning then runs over the same observed nodes.
Only incomplete markers are removed; all other pins, entries, classifications,
pending deletion metadata and rollups remain byte-for-byte semantic values.
No evidence is unlinked, restored, decrypted or executed.

Success has `closure_status = complete_closure_verified`. With no incomplete
markers, exact-HEAD checking still occurs under the lease, but the result is
the unchanged catalog/head with `no_incomplete_markers`; no CAS or evidence read
occurs and this status does not claim a newly verified closure. Stale HEAD
always returns `SCVDB_STORE_HEAD_ADVANCED`.

Missing, unregistered or deleted reachable nodes produce
`SCVDB_PIN_CLOSURE_MISSING`; restricted nodes produce
`SCVDB_PIN_CLOSURE_UNVERIFIED`. Actual corruption, scope, read-bound and lease
errors propagate. Unreadable unrelated live entries conservatively refuse
repair because ordinary retained-root planning also needs their actual edges.
Every failure leaves the catalog unchanged and releases the lease, subject to
the existing explicit `SCVDB_STORE_RELEASE_UNCERTAIN` error.

This reference owner is bounded to 256 catalog/closure nodes, 8 MiB content per
object and 32 MiB aggregate encoded CAS reads. Remaining byte allowance clamps
the reader before each read. Catalog metadata IO is separately bounded by its
existing codec/store; arrays retain at most the bounded evidence read set.
Lookup/deduplication is quadratic within the 256-node cap. No Operating B
throughput or peak-memory measurement is claimed. All verification runs while
holding SJ, intentionally preventing concurrent cooperative retention deletion.

Independent source scenarios cover actual restoration and registration, all
roots, transitive/shared edges, missing/corrupt/restricted bytes, stale HEAD,
ordinary pin preservation, unchanged failure state, no-marker retry and actual
subsequent retention planning. Tests are authored in the separate evidence
lane against this frozen API; the root integrates and reviews both commits.
