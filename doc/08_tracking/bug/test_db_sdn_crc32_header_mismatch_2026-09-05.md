# `doc/08_tracking/test/test_db.sdn` is committed with a stale CRC32 header

Date: 2026-09-05. Found while documenting the real `simple perf` workflow for
`.claude/skills/lib/perf_ladder.md`: `simple perf record` and `simple perf
explain` could not be exercised against a real test path because the test
database they read refuses to load.

## Symptom

The tracked file carries a `#sdn-crc32:` header that does not match its own
body, so every reader that honours the seal fails closed.

| | value |
|---|---|
| header line | `#sdn-crc32:1415345513` |
| body, recomputed | `3879582927` |
| file size | 126,843 bytes |

## Verification (repo's own method, read-only)

`scripts/check/reseal-sdn-crc32.shs:12` defines the convention as
"CRC-32/ISO-HDLC over the body (everything after the header line)", implemented
at `:26-28`. Reproduced with exactly that pipeline, without mutating the file:

```bash
f=doc/08_tracking/test/test_db.sdn
tail -n +2 "$f" | gzip -c -n | tail -c 8 | od -An -tu4 | awk '{print $1; exit}'
# -> 3879582927     while head -1 "$f" says #sdn-crc32:1415345513
```

Cross-checked with an independent CRC-32 implementation, which produced the same
`3879582927`. Two methods, one answer, so this is the file, not the measurement.

## Why it matters

`reseal-sdn-crc32.shs:7` states the intent plainly: "a body whose crc32 does not
match the header makes the header fail-CLOSED". That behaviour is correct and
should not be relaxed — the point of the seal is to refuse a hand-edited or
truncated database rather than silently trust it. The defect is that a file in
this state was committed.

Direct consequence measured today: `simple perf record <test-path> ...` and
`simple perf explain <test-path>` are unusable, which is why the perf ladder
documents them as BLOCKED rather than as verified commands.

## What is NOT yet established

- Whether the writer that regenerates this file reseals correctly, i.e. whether
  a full `simple test` run self-heals the header. `.claude/rules/structure.md`
  lists `test_db.sdn` as regenerated on every test run, but no test runner runs
  on this host (`bin/simple` is bootstrap-only), so this was not observed.
- Whether the mismatch is a stale seal after a hand edit, or a body truncated or
  merged without resealing. The body parses as SDN on inspection, which points at
  a stale seal rather than truncation, but that is inference, not evidence.
- Which commit introduced it. Not bisected.

## Unblock condition

Establish the cause before resealing. **Do not simply run
`reseal-sdn-crc32.shs` on it** — that would make the symptom disappear and
destroy the evidence for whichever producer wrote an unsealed body, which is the
actual defect. Once the producer is identified and fixed, reseal in the same
change and record the before/after CRC here.

## Related

- `scripts/check/reseal-sdn-crc32.shs` — the convention and the resealing tool.
- `.claude/skills/lib/perf_ladder.md` — records the resulting BLOCKED commands.
- `doc/08_tracking/bug/perf_regression_tests_4_mechanisms_red_2026-09-05.md` —
  separate, unrelated perf-gate issue found in the same pass.
