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

## 2026-11-07 — hold lifted (owner decision)

The "ONLY AFTER phase 3 passes" hold is superseded. Owner decision 2026-11-07:
`len()` counts code points; `byte_len()` stays bytes; `char_count()` stays an
alias; `s[a..b]` slices by code point (consistent with `s[i]`), while
`substring`/`slice(a, b)` stay byte-offset. Design + migration + rollout:
`doc/05_design/language/text/text_len_counts_characters_2026-11-07.md`.
The JIT `byte_len` boxing gap named above is fixed (`177e47d13d9`, verified on
the 2026-11-07 release seed: `byte_len()` prints 9 and `n == 9` is true).
Rollout: (A) docs, (B) byte-offset callers -> `byte_len()` + pure-Simple MIR
`byte_len`/`char_count` arms, (C) flip in interpreter + JIT + MIR together with
specs, (D) Phase 3 self-hosted verification.

## 2026-11-09 — native/JIT lane flipped (row text_len_bytes_vs_codepoint_index_bound_disagree_2026_11_03)

PR #7877 flipped the seed interpreter (and, observed in its spec, `substring` /
`slice(a, b)` too: they index by code point, superseding the "stay byte-offset"
wording above). This change flips the native/JIT lane to match, in both runtimes
and the pure-Simple twin, with parity:

- **Byte primitive unchanged:** `rt_string_len` stays bytes. It is the `(data,
  len)` text extern ABI pair, the `byte_len()` route and has ~300 internal
  callers; changing it would have been a silent ABI break.
- **Code-point surface:** `rt_string_char_count` (now the lowering target of a
  user-facing text `.len()`, with `rt_string_len`'s raw-pointer receiver
  fallback), `rt_len`'s text arm, `rt_slice`'s text arm (indices in code points,
  stride walks code points), `rt_string_find` / `rt_string_index_of` /
  `rt_text_find` (`start` and result in code points) / `rt_string_rfind`.
  Rust runtime `collections.rs`, C runtime `runtime_native.c`, twin
  `simple_core/core_string.spl`, and the interpreter extern emulations
  `interpreter_extern/sffi_string.rs` (`rt_string_find_fn` / `rt_string_rfind_fn`).
- **Codegen:** Cranelift `inline_runtime_len_value` (the inlined `rt_len`) and
  the typed `String.len` arm call `rt_string_char_count` for text; the LLVM
  `compile_inline_len` string arm does the same; pure-Simple MIR text `.len()` /
  `.len` field / `s[i]` bound lowerings emit `rt_string_char_count` instead of
  `rt_string_len` (the `byte_len` arm keeps `rt_string_len`).
- **ASCII fast path + memo:** one word-wise high-bit scan; the result is cached
  in the string header (`RT_STRING_FLAG_ASCII` Rust, new
  `RT_CORE_STRING_FLAG_ASCII` C) so ASCII text answers `len()` in O(1) after the
  first call. Non-ASCII text pays an O(n) code-point count per `len()` (the
  twin has the fast path but no memo bit).
- **Perf (C, clang -O2, 2M iters):** ASCII 64 B `rt_len` 13.5 -> 13.1 ns,
  ASCII 1 KiB 13.2 -> 12.5 ns, UTF-8 64 B 15.9 -> 46.8 ns; `rt_string_char_count`
  ASCII 1 KiB 5127 -> 14 ns; `rt_slice(2,10)` 221 -> 200 ns (ASCII 64 B).
  JIT (`run`, 2M `.len()` on a 64 B literal): see the PR body for the memoized
  numbers; the pre-memo build measured 6 -> 33 ns (ASCII) and 7 -> 153 ns
  (UTF-8) per call.
- **Evidence:** `src/runtime/test/rt_text_len_slice_codepoint_selfcheck.c` (55
  checks; FAILs check 2 `rt_len == 5` on the pristine runtime), Rust
  `text_len_slice_codepoint_tests` (4 tests), and
  `test/01_unit/language/text_index_branches/text_len_slice_native_adr005_spec.spl`
  (8 of 11 examples red on the 2026-11-08 release seed, green on the rebuilt
  seed).
- **Left open:** baremetal C cores (`examples/09_embedded/.../baremetal_*`) do
  not define `rt_string_char_count`, so the Cranelift inline keeps the byte load
  there (`string_cp_len_ref` returns `None` when `ctx.baremetal`); Phase 3
  self-hosted verification (stage2/stage3 compile the pure-Simple MIR change).
