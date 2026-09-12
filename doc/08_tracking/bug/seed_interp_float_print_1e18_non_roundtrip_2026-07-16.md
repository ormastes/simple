# Seed interpreter: print(1e-18) emits non-round-tripping "0.00000000000000000"

- **Date:** 2026-07-16
- **Component:** Rust seed interpreter float formatting (`bin/simple run`)
- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Found by:** native-build correctness campaign, parity case `float_edges`
  in `scripts/check/check-native-seed-parity.shs`

## Symptom

```spl
fn main() -> i64:
    print(-0.0)
    print(0.0 / 0.0)
    print(0.000000000000000001)
    return 0
```

| line | seed `run` | native-build | verdict |
|------|------------|--------------|---------|
| `-0.0` | `-0.0` | `-0.0` | agree |
| `0.0/0.0` | `NaN` | `NaN` | agree |
| `1e-18` | `0.00000000000000000` | `0.000000000000000001` | seed WRONG |

The seed's `0.00000000000000000` parses back as `0.0` — the value is lost
entirely (non-round-trip). Native's positional `0.000000000000000001` parses
back to exactly the same f64 as `1e-18`.

## Class

Same non-round-trip formatting defect family as the seed printing `0.1` as
`0.09999999999999998` (parity case `float_print`, already NATIVE-AUTHORITATIVE).
The seed appears to format with a fixed number of fractional digits instead of
shortest-round-trip.

## Harness impact

`float_edges` reclassified PARITY -> NATIVE-AUTHORITATIVE (expected
`-0.0NaN0.000000000000000001`) in `check-native-seed-parity.shs` on 2026-07-16.
Fix belongs in the seed's f64-to-string (shortest round-trip, e.g. Ryu/`{}`
formatting) when the seed is next rebuilt.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
