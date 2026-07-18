# Bug: `text.len()` returns bytes but `text[i]` indexes codepoints

**Date:** 2026-07-02
**Status:** Open (investigated, no code change yet — semantics decision required)
**Severity:** High — any `while i < s.len(): s[i]` loop panics on non-ASCII input
**Crash precedent:** spec-coverage crashed with `string index out of bounds: index is 732 but length is 732`; fixed at call site by switching to `.chars()` (`fix(cli_util): parse_csv_fields codepoint-safe indexing` — 11 similar commits in history).

## Repro

```simple
s = "abc—def"        // em-dash is 3 UTF-8 bytes
s.len()              // 9  (bytes)
s.chars().len()      // 7  (codepoints)
s[3]                 // "—" (4th CODEPOINT — indexing is codepoint-based)
s[6]                 // "f" (7th codepoint)
// while i < s.len(): s[i]  → i reaches 7 with len()==9 → panic
// "string index out of bounds: index is 7 but length is 7"
```

Verified 2026-07-02 on `bin/simple run` — identical on interpreter and JIT paths.

## Semantics matrix (all layers)

| Layer | `len()` | `s[i]` returns | `s[i]` bounds unit | Verdict |
|---|---|---|---|---|
| Rust seed interpreter (`src/compiler_rust/compiler/src/interpreter_method/string.rs:21`; `interpreter/expr/collections.rs:98-127`) | **bytes** (`s.len()`) | **codepoint** (`chars().nth`) | codepoint (`chars().count()`) — panic msg at `collections.rs:91` | MISMATCH (len vs index) |
| Rust seed pattern-match fallback (`interpreter_helpers/method_dispatch.rs:33`) | **codepoints** (`chars().count()`) | — | — | third, inconsistent `len` copy |
| Rust seed runtime crate (`src/compiler_rust/runtime/src/value/collections.rs:1462` `rt_string_len`; `:1658-1681` `rt_string_char_at`) | **bytes** | **codepoint** (`chars().nth`) | **byte** length guard | doubly mixed; fails safe (NIL) for i in [cp_len, byte_len) |
| Self-hosted interpreter (`src/compiler/10.frontend/core/interpreter/eval_access.spl:105-116`, `eval_methods.spl:394-402` `char_at`) | **bytes** | **codepoint** | **byte** (`idx < s.len()`) | MISMATCH; wrong-unit guard on a codepoint op |
| Self-hosted lowering (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:250-258`; C backend `cg_expr.spl:607,616`) | **bytes** (`rt_string_len` / `spl_str_len`) | — | — | len is a byte intrinsic everywhere |
| Native C runtime (`src/runtime/runtime_native.c:710` `rt_string_len`; `:726-730` `rt_string_char_at`) | **bytes** | **byte** (raw `data + index`, 1 byte) | byte | self-consistent (bytes/bytes) but DIVERGES from interp/JIT observed behavior |
| Pure-Simple core runtime (`src/runtime/simple_core/core_string.spl:554-557`) | **bytes** | **byte** (comment: "byte-indexed (not UTF-8 codepoint-indexed like the Rust version)") | byte | self-consistent; divergence is documented in-code |
| stdlib escape hatches (`src/lib/.../utf8.spl:249,253,268`) | `text_byte_len`, `text_codepoint_len` (cached), `text_codepoints` | — | — | explicit-unit API already exists |

**Root cause:** `.len()` is lowered to a byte-count intrinsic in every layer, while the `[]` operator (and the interpreter `char_at`) decode UTF-8 codepoints. The observed panic ("index is N but length is N") comes from the codepoint-unit bounds check firing exactly when `i` reaches `chars().count()` while the loop bound is the larger byte count. Additionally, the interpreter/JIT (codepoint `[]`) and the native C / pure-Simple runtime (byte `[]`) disagree with each other — a second, latent divergence for AOT-compiled code.

## Documented intent

- `doc/07_guide/quick_reference/syntax_quick_reference.md`, `doc/glossary.md`: **no statement** of byte-vs-codepoint semantics for `text.len()` or `text[i]`.
- `doc/06_spec/01_unit/lib/text/text_length_spec.md` + `text_index_slice_spec.md` (red-phase, Phase 5, from `test/01_unit/lib/text/text_length_spec.spl`): planned `Text`/`TextView` type with **explicit named units** — `len_bytes`, `len_codepoints`, `len_graphemes`, `cp_at(i)` — i.e. the documented direction is to *remove* the ambiguous overloads, not to pick a unit for them.

Since no current-semantics spec exists, no single layer is "clearly out of spec"; per investigation rules, **no code change was made**.

## Blast radius (approximate)

- `while i < X.len(): ... X[i]` pattern: ~10,441 raw hits across `src/` + `test/`; by variable-name heuristic ~**760 text-ish** (s/str/text/line/word/input/content) vs ~550 collection-ish; sampled text-ish loops (regex.spl, cli_util.spl, http/accept_encoding.spl, io/buffer.spl) are ASCII-scanning loops that break on non-ASCII input under codepoint-index/byte-len.
- Byte-dependent `.len()` uses (buffer sizing, memcpy, sockets, hashing, fwrite): ~**415 files** — these REQUIRE byte semantics; making `len()` codepoint-based would silently corrupt them and cost O(n) per call.

## Recommendation

**Target semantics: both `len()` and `[i]` byte-based (UTF-8 code units), with `.chars()` / `text_codepoint_len()` as the explicit codepoint API.** Rationale:

1. `len()` is already bytes in every layer and ~415 files depend on byte semantics; flipping it is the larger, slower (O(n)) and more silently-corrupting change.
2. The native C runtime and pure-Simple core runtime are *already* byte/byte self-consistent — the codepoint `[]` in the interpreters is the outlier.
3. Matches mainstream precedent (Rust, Go: len = storage code units; codepoint access via explicit iterator).
4. Aligns with the Phase-5 `Text`/`TextView` spec: explicit `len_bytes`/`len_codepoints`/`cp_at` supersedes the overloads anyway.

Cost: codepoint-indexing users of `s[i]` on non-ASCII break — but such code is *already broken* today (the `while i < s.len()` loops panic), and byte-`[]` at least makes ASCII code uniformly correct and non-ASCII deterministic per-layer.

## Migration plan (safe order)

1. **Lint first (no behavior change):** add a lint flagging `s[i]` / `while i < s.len()` on `text` operands, suggesting `.chars()` (codepoint intent) or byte-explicit APIs. Burn down the ~760 text-ish loops.
2. **Fix the wrong-unit guards** (contained, behavior-preserving for valid inputs): self-hosted `eval_access.spl:108-116` and `eval_methods.spl:394-402`, and seed `rt_string_char_at` (`compiler_rust/runtime/.../collections.rs:1658`) currently guard codepoint ops with byte length — make guard unit match the op's unit so out-of-range is reported consistently.
3. **Switch `[]` to byte-based** in seed interpreter + self-hosted interpreter in one change, gated by full spec run + bootstrap (`bin/simple build bootstrap`), converging on the native runtime's semantics.
4. **Land Phase-5 `Text`/`TextView`** (`len_bytes`/`len_codepoints`/`len_graphemes`/`cp_at`) and migrate user code to explicit units; eventually deprecate bare `s[i]` on `text`.
5. Document the chosen semantics in `doc/07_guide/quick_reference/syntax_quick_reference.md` and `doc/glossary.md`.
