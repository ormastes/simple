# text.len() returns bytes, violating ADR-005 (row text_len_codepoint_switch_2026-11-03)

- **ID:** text_len_codepoint_switch_2026-11-03 (existing staging row; audit added 2026-11-06)
- **Severity:** P2 — **Status:** open (switch held until phase 3 passes)
- **Decision:** ADR-005 (`doc/04_architecture/adr/ADR-005-text-index-yields-char.md`, owner 2026-11-06):
  `s.len()` = code points, `s.byte_len()` = bytes. No new methods, no `count()` alias.
- **Related:** JIT `byte_len` boxing fix (separate PR, other worker).

## Repro (seed `bin/simple.exe run`, release 0b2c3d015b7)

```
fn main():
    val s = "héllo€"
    val n = s.byte_len()
    print "len={s.len()} byte_len={s.byte_len()} eq={n == 9} add={n + 0}"
```

Observed: `len=9` (expected 6 per ADR-005). Also, in the seed's default run mode,
`byte_len()` interpolates as `<invalid-heap:0x9>` and `n == 9` is `false`, while
`<`, `+` and loop bounds on it work (`n + 0` = 9) — the JIT boxing bug.

## Audit of byte-dependent text `.len()` callers (grep/sed/awk only)

Method: per file in `src/compiler` + `src/lib` that calls `X.byte_at(`, every
`X.len()` on the same receiver names (157 files). Arrays/lists/dicts are excluded
by construction (receiver must be `byte_at`-indexed text).

| area | inspected | relational bound | `==`/`!=` | offset/arith/assign | comment |
|---|---|---|---|---|---|
| src/compiler | 210 | 96 | 35 | 77 | 2 |
| src/lib | 331 | 181 | 58 | 84 | 8 |
| **total** | **541** | 277 | 93 | 161 | 10 |

- **Switched: 6** — `src/lib/nogc_sync_mut/lsp/lsp_location.spl` lines 26, 32, 51, 54, 64, 67
  (pure byte_at scans, relational bounds only; module is editor-only, not imported by
  `src/compiler` or the test runner).
- **Left: 535**
  - 10 comments.
  - 208 compiler sites: bootstrap path. The pure-Simple MIR lowering lowers `byte_at`
    (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4970`) but has no
    `byte_len` arm, and `.byte_len()` has 0 existing callers in `src/compiler`/`src/lib`;
    switching would put an unlowered method on the stage2/stage3 path.
  - 93 equality sites (all areas, incl. compiler): seed JIT `byte_len` `==` returns false (boxing bug).
  - remaining lib sites (relational/offset; 3 more in lsp_location are mixed with
    `substring`/`index_of` or are `==`): stdlib is compiled by stage2/stage3 with the same
    missing lowering — deferred to the switch PR.
- Code-point-safe / ASCII-display callers outside this receiver set (the other ~48.5k raw
  `.len()` hits are mostly arrays) were not individually classified; they need no change.

## Prevention

`test/01_unit/app/lsp/lsp_location_spec.spl` — "parses line and column after multibyte
path characters": pins `byte_len()` = 9 on `"héllo€"` and the switched scan on a non-ASCII
path. It passes today *only because len() == byte_len() now*; it guards the switch.

## Next step

Switch `len()` to code points in interpreter, JIT and native **with parity specs, ONLY AFTER
phase 3 passes** (compiler callers are on the bootstrap path). Before that: land the JIT
`byte_len` boxing fix (separate PR, another worker) and add a `byte_len` arm to pure-Simple
MIR lowering, then switch the 535 remaining byte-dependent sites listed by this audit's method.
