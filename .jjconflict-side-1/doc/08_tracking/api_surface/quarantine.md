# API Guard Quarantine — Pre-existing Broken Specs

These specs were broken **before** any perf-umbrella work started, due to
refactor commit `cd46a9463a4` (missing E0410 export declarations in
`std.http_server.*` modules).  They must not be counted as perf-introduced
regressions.

## Quarantined Specs

| Spec | Error | Confirmed broken |
|------|-------|-----------------|
| `test/01_unit/lib/http_server/rate_limit_spec.spl` | `E0410: module 'std.http_server.rate_limit' does not export 'default_rate_limit_config'` | yes — 2026-06-13 |
| `test/01_unit/lib/http_server/request_validation_spec.spl` | `E0410: module 'std.http_server.request_validation' does not export 'validate_request_path'` | yes — 2026-06-13 |
| `test/01_unit/lib/http_server/security_headers_spec.spl` | `E0410: module 'std.http_server.security_headers' does not export 'default_security_headers_config'` | yes — 2026-06-13 |

## Verification

Each was confirmed via `bin/simple check <spec>` on 2026-06-13:

```
rate_limit_spec.spl:12:1: error[E0410]: module 'std.http_server.rate_limit'
  does not export 'default_rate_limit_config'

request_validation_spec.spl:12:1: error[E0410]: module 'std.http_server.request_validation'
  does not export 'validate_request_path'

security_headers_spec.spl:12:1: error[E0410]: module 'std.http_server.security_headers'
  does not export 'default_security_headers_config'
```

Root cause: the refactor added the implementation symbols but omitted the
`export` statement in each sub-module's `__init__.spl`.  Fix: add the three
`export` lines.  Until fixed, these specs are excluded from the AC-8 guard.

## Guard behaviour

`check-api-arch-guard.shs` does **not** run these specs.  The quarantine is
documentation only — it exists so future engineers understand why these three
specs are red and do not panic that the perf work broke them.
