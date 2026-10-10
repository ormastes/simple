# Item 6 semantic module action reuse (2026-10-10)

Status: source change and focused regression probe prepared; runtime and performance qualification pending.

The prior module action digest included SCV revision, commit, tree and the
whole inventory digest. Every source edit changed those generation-wide fields,
therefore every module action key changed. The package archive lookup uses
that key, so a stable workspace root alone could not yield unchanged-module
archive hits. This contradicted the selected semantic reuse design.

The cold builder now emits a domain-separated v2 module action key from
producer, stable workspace root, variant/scope and the entry's own source,
metadata, ABI, initializer, provider, manifest, topology and imports. The
generation index still binds SCV revision, commit, tree and inventory. Archive
load still checks the action key, producer/root/variant, normalized metadata,
and dependency interface digests. Validation and the grouped warm route accept
legacy snapshot-bound v1 keys for migration, while new publication emits v2.
An unchanged module can reuse its action across snapshot generations; source
or variant changes still produce a different key. Old v1 archives naturally
miss on the first v2 publication, then can be replaced.

The existing native CAS probe now asserts legacy validation, v2 stability
when only SCV generation fields change, and v2 sensitivity to source and
variant changes. It also publishes a v2 generation. The probe has not run on this source. The historical admitted Stage 2
first stopped while discovering `windows_redirected_process.spl:8:20`
(`expected Fn, found Colon`). A separate sparse test projection excluded
the unneeded conditional platform files, but code generation then stopped in
`process_ops.spl` at undeclared `WINDOWS_REDIRECTED_TOKEN_BASE`. The
current-source Stage 2 binary was built by a separate bootstrap session but
was not admitted: planner execution ended with
`bootstrap-policy-error: receipt-write-failed`. No further probe retry was
made after those bounded attempts. No full cold/warm transition, application
behavior, or paired time/RSS result is claimed. The event-to-module hint gap in the root-generation report also
remains open.
