# check-extern-return-shape.shs selftest depends on sort locale (2026-11-28)

Status: open (observed while verifying PR #12418, Windows Git Bash)

`sh scripts/check/check-extern-return-shape.shs --root .` printed
`selftest: clean fixture must PASS ...: CHANGED: rt_nom baseline {i64? | Nom?} now
{Nom? | i64?}` then `FAIL`, although the same selftest passed earlier in the session
(PR #12359). The shape set is built with `sort -t <tab> -k1,1 -k2,2 -u` (line ~131) and
`sort` elsewhere, none under `LC_ALL=C`. Under a locale-aware collation `i64?` sorts
before `Nom?`; under the C locale uppercase sorts first. The fixture baseline assumes one
order, so the gate result depends on the caller's locale (and can falsely FAIL or pass).

Fix: run every `sort` in the script (and the matching generator for the baseline) with
`LC_ALL=C`, and add a selftest fixture whose shapes differ only in case. Baseline file
ordering must then be regenerated with the same locale if any row changes.
