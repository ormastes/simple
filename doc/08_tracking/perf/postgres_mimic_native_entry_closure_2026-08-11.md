# PostgreSQL-mimic native entry closure tractability

Status: improved structurally; native artifact remains unverified.

## Frozen failed baseline

- Entry: `src/app/postgres_mimic_server/main.spl`
- Mode: native build with `--entry-closure` on the Linux host
- Result: no artifact after 10m37s; peak RSS 2.76 GiB
- Evidence classification: failed diagnostic run, not executable proof

The identical full build must not be repeated until a bounded closure probe shows
that the closure completes within its budget.

## Root-cause evidence

The daemon's required `PureDatabase` capsule is intrinsically broad: its two
implementation sources total 193,562 source bytes and retain SQL, MVCC, FTS and
page-summary support. Those imports are functional server scope and must not be
removed to manufacture a smaller build.

The compiler entry-closure loader now maintains `closure_queued_paths` in
addition to processed/logical source sets. A resolved physical source is added
to the scan queue only on the first physical-path encounter. This prevents
shared re-export paths from multiplying parse/import-scan work before a source
becomes processed.

The daemon now imports the exact `server`, `linux_server`, and `connection`
owners instead of the two-level `std.database.postgres_mimic` umbrella. Runtime
features are unchanged; the edit removes re-export aliases from the entry root
and makes its required closure explicit.

## Admission contract

Before retrying the full native link, capture an isolated, cache-preserving
closure/build receipt under `build/native_probe/` with compiler identity,
source manifest, wall time, peak RSS, completed/total physical sources,
files/second, exit status, and artifact hash when present. Use
`SIMPLE_NO_STUB_FALLBACK=1`; do not share a writable cache with another build.

The next full retry is admitted only if a bounded trace reaches closure
completion without duplicate physical paths and projects peak RSS below 2 GiB.
Success still requires the native daemon artifact and live pgwire smoke; a
static import contract is not success evidence.

## 2026-08-11 strict-gate audit

The production source universe is now pinned to `src/app` plus `src/lib` with
`src/app/postgres_mimic_server/main.spl` as the sole entry. `src/compiler` is
not imported by this server and must not be supplied as a source root: doing so
widens discovery without adding a reachable server owner. The equivalent web
server gate uses the same two-root contract.

`scripts/check/build-postgres-mimic-server-native.shs` now performs compiler
authority admission before starting this closure and forbids unresolved-stub
fallback. The single bounded gate probe in this audit used `bin/simple` and
failed in 0.2 seconds with exit 6:

```text
FAIL: production build requires a usable pure-Simple self-hosted compiler; authority probe rejected: bin/simple
```

Therefore the current blocker precedes server parsing, closure discovery, MIR,
and linking: there is no admitted pure-Simple self-hosted compiler at the
requested path. This result is a fail-fast authority receipt, not native server
build evidence. No second or full closure build was attempted.
