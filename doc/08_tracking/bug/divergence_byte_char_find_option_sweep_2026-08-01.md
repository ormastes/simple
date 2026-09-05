# Divergence sweep: byte-vs-char + find/rfind-as-Option — IN PROGRESS

- **Id:** divergence_byte_char_find_option_sweep_2026-08-01
- **Status:** In Progress — NOT YET DONE (ongoing; yield decreasing, not zero)
- **Severity:** P2 — silent product-correctness divergences across `src/**`
- **Component:** cross-cutting (`src/compiler`, `src/lib`, `src/app`)

## Scope

Cheap read-only parallel scans (small models) over the owned tree, oracle-verified
per finding against the Rust seed, fixing silent divergence-family bugs:
- **byte-vs-char** — `text.len()` (bytes) mixed with char-indexed `[i]`/`char_at`/
  `char_code_at`; fix = `.chars()` (char-array) or `slice(i,i+1)` (byte-consistency).
- **find/rfind/index_of as Option** — they return a raw i64 (-1 = miss), NOT an
  Option; `if val`/`.?`/`match Some/nil`/`?? default` all misbehave. Additionally
  the tag-boxed result slices wrong as a `text[:idx]` bound — use `.substring()`.

## Landed so far (2026-08-01)

- `4beaa207810` — JS delimiter gate + SQL LIKE prefix/matcher (3 fixes)
- `29687ff0d530` — treesitter heuristic + macro_registry expand (2 fixes)
- `30fbcdc0f00` — find→bracket-slice family enumerated (5 more sites: KMS SigV4,
  formatter, doc_gen, infra, deployment automation)
- (earlier waves this session: `95bab2150be`, `4149aa7d01b`, `62dc9efd4ad`)

## Not yet done

- Scan coverage is not exhaustive: several `src/lib` / `src/compiler` subtrees
  remain unscanned; yield is decreasing (Wave 11 = 2 fixes / 5 lanes, 3 clean)
  but not zero. Continue in waves until a full pass returns clean.
- Deferred site: `module_lowering.spl:176` (native-codegen-sensitive) — see
  `doc/08_tracking/bug/module_lowering_byte_vs_char_sanitizer_2026-08-01.md`.
- Byte-semantic rewrites (to_bytes/base64/checksum/crypto signing) still need a
  real UTF-8 byte accessor; the char-array fix yields codepoints, not bytes.

This sweep is product-correctness only; it does **not** unblock pure-Simple
self-host (that umbrella blocker is
`doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`).
