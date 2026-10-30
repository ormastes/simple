# RSS guard Windows compiler identity publication race (2026-10-27)

Status: focused publication regression PASS; frozen campaign retry pending;
canonical bug database registration **PENDING**.

## Failure evidence

In `D:/dev/simple-all-objects-phase2-20261027`, the frozen object campaign
`c718ec0c9fbc4f25bdfe45181b7c4bc9` recorded row
`9c3b7f661a37c648102e78c417030aa8d3fd53850f503b27f17c0f22b4b3a110`
(`src/app/_cg/f06/main.spl`) as exit 89 during RSS guard helper installation.
Its supervisor log at
`build/object-campaign/objects/c718ec0c9fbc4f25bdfe45181b7c4bc9/9c3b7f661a37c648102e78c417030aa8d3fd53850f503b27f17c0f22b4b3a110/supervisor.log`
reports `cannot record compiler identity` at the then-current
`scripts/resource/process-tree-rss-watchdog.pl:825`. The corresponding RSS receipt
`build/object-campaign/rss/c718ec0c9fbc4f25bdfe45181b7c4bc9/9c3b7f661a37c648102e78c417030aa8d3fd53850f503b27f17c0f22b4b3a110.rss.env` records
`root_pid=0`, `session_id=0`, blank helper identity fields, and
`session-helper-install-failed`; the row directory contains no workload spec or
compiler log. The Simple compiler did not start.

At the same timestamp, `D:/dev/simple-all-objects-phase2-20261027/.simple/storage/cache/bootstrap-session-helper`
contained both
`identity-f928c779fb1222d132064ccdeddc0226652054b7cbdbaba146639145d30c248d.txt`
and `identity-f928c779fb1222d132064ccdeddc0226652054b7cbdbaba146639145d30c248d.txt.new.63739`.
Both files were 253 bytes and had SHA-256
`35377A6BF84908A7867B647415CC2C7066CD693D7D903C6A7222D1CE74FCFDEC`.
This supports a concurrent identity publication collision. The old code merged
`close` and `rename` failures into one generic error, so the exact failed
operation was not recorded. The repaired publication mechanism passes the
focused regression below, but the original failure remains a race hypothesis.

## Repair

The candidate writes an exclusive, unique temporary file in the cache and
publishes it with a same-directory hard link, which cannot overwrite an
existing winner. A failed publish is accepted only when the destination is a
regular non-symlink file whose complete bytes equal the identity queried by
this process and still identify clang. Other failures are reported separately
and only the caller's temporary file is removed. There is no rename fallback.

The focused regression invokes this production helper from two synchronized
child processes against an empty cache, then checks divergent, truncated, and
absent destination failures. It passed with exit 0 using
`perl scripts/check/tests/session_helper_identity_cache_publication_test.pl`;
the watchdog also passed `perl -c`. This validates publication behavior and the
fail-closed controls, but does not prove the original campaign failure was a
race. Neither command invokes the Simple compiler or rebuilds the pinned
producer. The frozen campaign retry remains pending.
