# Stage 4 parser rejects large decimal u64 literals through its i64 path

- **Status:** FIXED
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02, Stage 4 phase 2
- **Area:** pure-Simple hash constants

The full CLI parser rejected the canonical FNV-1a offset basis even with a
`u64` suffix because the decimal token was range-checked as i64 first. Keep the
exact unsigned bits using the canonical hexadecimal spelling. The adjacent GPU
event hash owner uses the same basis and is changed with it so the next closure
shape cannot rediscover the same parser boundary.
