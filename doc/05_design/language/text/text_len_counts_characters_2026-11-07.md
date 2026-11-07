# Design: text `len()` counts characters (code points)

- **Status:** accepted (owner decision 2026-11-07). Supersedes the "switch held
  until phase 3 passes" hold in ADR-005 § Staging and in
  `doc/08_tracking/bug/text_len_codepoint_switch_2026-11-03.md`.
- **Scope:** language semantics of text length, text indexing, text slicing;
  seed interpreter, seed JIT (Cranelift), seed LLVM lane, pure-Simple MIR
  lowering (stage2/stage3), stdlib and app callers.
- **Related:** ADR-005 (`text[i]` yields `char`), bugs
  `text_len_bytes_vs_index_codepoints_2026-07-02`,
  `text_len_substring_bytes_but_index_chars_2026-08-30`,
  `text_len_codepoint_switch_2026-11-03`,
  `jit_text_byte_len_untagged_int_boxing_2026-11-06` (fixed, `177e47d13d9`).

## Where the change was "staged"

There is no code flag. The staging is documentary only: ADR-005 § Staging,
`syntax_quick_reference.md` ("`.len()` counts code points (staged)"), and the
2026-11-06 audit in the `text_len_codepoint_switch_2026-11-03` bug record
(541 byte-dependent `len()` sites, 6 switched, hold until phase 3). This design
lifts the hold and defines the rollout.

## Rule

| expression | unit | engine today | target |
|---|---|---|---|
| `s.len()`, `s.length()` | **code points** | bytes (interp + JIT) | code points |
| `s.char_count()` | code points | code points | unchanged (alias of `len()`) |
| `s.byte_len()` | bytes | bytes (JIT boxing fixed `177e47d13d9`) | unchanged |
| `s[i]` | code point (`char`) | code point | unchanged |
| `s[a..b]`, `s[a:b]`, `s[a..=b]` | **code points** | bytes (interp + JIT, `rt_slice`) | code points |
| `s.substring(a, b)`, `s.slice(a, b)` | bytes | bytes | unchanged (explicit byte API) |
| `s.byte_at(i)`, `s.index_of(..)`, `s.char_code_at(i)`, `s.to_bytes()` | bytes | bytes | unchanged |
| `s.chars()` | code points | code points | unchanged |

One rule: **the index/slice/len family (`s[i]`, `s[a..b]`, `len()`) is
character-based; the named byte family (`byte_len`, `byte_at`, `substring`,
`slice`, `index_of`, `char_code_at`, `to_bytes`) is byte-based.** A caller
never mixes a `len()` with a `byte_at()` on the same receiver.

Why `substring`/`slice` stay byte-based: every lexer and tokenizer in the
tree (SDN, JSON, TOML, the compiler's own lexer, `lsp_location`) scans with
`byte_at`/`index_of` and cuts with `substring`; the interpreter comment at
`interpreter/expr/collections.rs:451` records that making these character-
based silently corrupted every byte-offset cut on multi-byte text. The
operator slice `s[a..b]` is the only slicing spelling that must agree with
`s[i]`, because `s[a..b]` and `s[i]` share the index space in the reader's
mind; a method named `substring(byte_start, byte_end)` can carry its unit in
its documentation.

### Bounds

- `s[i]`: valid for `-n <= i < n` where `n = s.len()` (code points); negative
  counts from the end. Out of range follows ADR-005/ADR-006 (index error;
  PANIC-W-INDEX when unproven).
- `s[a..b]`: `a`, `b` are code-point offsets, normalised and clamped to
  `0..=n` exactly as array slices are (negative from the end, `a >= b` gives
  `""`). A slice never splits a code point, so the result is always valid
  UTF-8 and never needs `StrBytes`.
- `substring(a, b)` / `slice(a, b)`: byte offsets, unchanged (clamp to
  `0..=byte_len()`; a split code point yields raw bytes as today).

### Complexity

`len()` becomes O(n) on non-ASCII text (`rt_string_char_count`), O(1) on
ASCII when the runtime's ASCII fast path applies. `for i in 0..s.len(): s[i]`
is O(n^2) on non-ASCII; the existing lint warns and `s.chars()` is the loop
form. If a measured regression appears on a hot path, record it as a bug and
cache an `is_ascii`/`char_count` word on `RuntimeString` rather than reverting.

## What changes in code

1. Seed interpreter: `interpreter_method/string.rs:23` (`"len" | "length"`
   split from `"byte_len"`), `interpreter/expr/calls.rs:1062` (property
   form), `interpreter/expr/collections.rs:451` (`Value::Str` slice by code
   point; `StrBytes` receivers stay byte-based).
2. Seed JIT/LLVM: `codegen/instr/calls.rs`, `closures_structs.rs`,
   `codegen/llvm/functions.rs` — route text `"len" | "length"` to
   `rt_string_char_count`; `rt_slice` string branch slices by code point.
   `rt_len`/`rt_string_len` keep returning bytes (they back `byte_len` and
   `rt_*` byte externs).
3. Pure-Simple MIR (`50.mir/_MirLoweringExpr/method_calls_literals.spl`):
   add `byte_len` and `char_count` arms (today none exist, so a stage2/3
   compile of a `byte_len()` caller is unlowered); route text `len` to
   `rt_string_char_count`.
4. Callers: every `len()` used as a byte offset/size switches to `byte_len()`
   BEFORE the flip (audit method: receiver co-occurs with `byte_at`,
   `substring`, `index_of`, `char_code_at`, `to_bytes`, an `rt_*` byte extern,
   or buffer/frame sizing). Text `s[a..b]` with byte offsets switches to
   `s.substring(a, b)`.

## Migration guide for callers

| you wrote | you meant | write |
|---|---|---|
| `while i < s.len(): s.byte_at(i)` | byte scan | `while i < s.byte_len(): s.byte_at(i)` |
| `s.substring(i, s.len())` | byte tail | `s.substring(i, s.byte_len())` |
| `buf.write(s, s.len())`, length-prefixed frames, base64/hex sizing | bytes | `s.byte_len()` |
| `s[p..q]` where `p`,`q` came from `index_of`/`byte_at` | byte cut | `s.substring(p, q)` |
| `for i in 0..s.len(): s[i]` | characters | keep, or `for c in s.chars()` |
| `s.len() == 0`, `s.len() > 0` | emptiness | keep (`is_empty()` preferred) |
| `s.char_count()` | characters | keep (alias) |

## Rollout

| phase | PR | content | behaviour change |
|---|---|---|---|
| A | docs(lang) design (this) | rule, migration, rollout | none |
| B | fix(lib,app,compiler) byte-offset callers | `len()` -> `byte_len()` at audited byte sites; `s[a..b]` byte cuts -> `substring`; pure-Simple MIR `byte_len`/`char_count` arms | none today (`len()==byte_len()`) |
| C1 | feat(lang) len flip | interpreter + JIT + LLVM + runtime `rt_len` + pure-Simple MIR text `len`/`length` to code points; specs RED->GREEN; collateral text/utf8/base64/json/sdn/cbor/crypto specs green | `len()` counts characters; `s[a..b]` still bytes |
| C2 | fix + feat slice flip | audit text `s[a..b]`/`s[a:b]` with byte offsets (receiver co-occurs with `byte_at`/`index_of`/`substring`) -> `substring(a, b)`; then `rt_slice` string branch + interpreter `Value::Str` slice to code points | `s[a..b]` counts characters |
| D | Phase 3 | self-hosted stage2/stage3 relink and `bin/simple test` on the self-hosted binary | verification-pending until the bootstrap lane runs |

C1 and C2 are each a single PR so that interpreter and JIT never disagree
within a phase. They are split because the slice migration is a separate
audit (byte-offset `s[a:b]` cuts in the JSON/TOML tokenizers and
`string_core`); between C1 and C2 the quick reference marks `s[a..b]` as
"bytes until C2". Any collateral spec regression in C1/C2 is a missed
byte-offset caller: fix the caller (`byte_len()`/`substring`), never the spec.

## Specs

- `test/01_unit/lib/text/text_len_units_spec.spl` — gains `len()` assertions
  (`"héllo€".len() == 6`, `s[s.len()-1] == '€'`, `s[1..3] == "él"`) in phase C.
- Collateral (must stay green through B and C): `utf8_bulk_validation_spec`,
  `base64*`, `cbor_types*`, sdn specs, json specs, `string_core_charcode_spec`,
  `test/01_unit/lib/common/text*`.
