# Parse fiber errors report child success

Bug ID: `parse_fiber_errors_report_child_success_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE**; native verification remains pending; not closed.

Upstream `d2ab53c494f2a1ddca409ea91b524653084ff741`, merged in
`64d0575f7b5e1b9219a6f09ab45ff5f1d042f79f`, counts FileFiber parse errors but
returns `true` from `_driver_run_parse_fibers`. The only wrapper caller in
`src/app/cli/parse_shard_main.spl` maps true to exit0, so an errored parse child
reports success.

The coordinator uses these children for best-effort cache warming and reparses
remaining work in the final build. The demonstrated source defect is therefore
false-success **child diagnostic status**, not proven whole-build silent acceptance.
Ignored frontend scope-publication results also exist in the ordinary parser and
are not established as a new fiber-only regression.

An applied uncommitted one-line candidate in
`src/compiler/80.driver/driver_parse_shard_entry.spl` returns `errors == 0` after
the existing summary, leaving retries/fallback and scope policy unchanged.
The source/interface review is complete; no error-path run or native validation
has been performed. Existing file-fiber tests need a real parse-child status
failure oracle before this report can be closed.

Retained upstream/source assessment:
`/Users/ormastes/wt/bootstrap-pattern-provenance-20261025/build/verify/upstream-570fc936-integration-assessment-20261025/`.
No compiler-producer or execution receipt is claimed for this source-only finding.

Owner source SHA256 at `64d0575f7b5e1b9219a6f09ab45ff5f1d042f79f`:

- `src/compiler/80.driver/driver_parse_shard_entry.spl`: `a94eb38d82e57fa2df5646de5a2c0e85640db8fad1f8b06b01c0f25119e0906a`.

Applied candidate source SHA256 when recorded (uncommitted, not a qualification):

- `src/compiler/80.driver/driver_parse_shard_entry.spl`: `39718f721be257e9a197562fee84cb6f811853fc111200ef74edd22bdef543ad`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/80.driver/driver_parse_shard_entry.spl`: `39718f721be257e9a197562fee84cb6f811853fc111200ef74edd22bdef543ad`.
