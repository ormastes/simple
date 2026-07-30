# Seed redeploy readiness report — 2026-07-30

**Recommendation: GO** (revised). The single blocking regression found in
the first pass — interpreter text slices substituting U+FFFD for
mid-codepoint fragments — is fixed in the same commit as this revision.
A fresh candidate built from a tip that includes that fix plus the
Result/try-operator and HIR alias/module-surface work passes every gate:
the three json escape specs FLIP green, byte indexing STAYS green, and
the whole regression set is clean. Deployment steps are written out
below but NOT executed — the deploy call is the user's.

## Candidate identity (PROVED)

- Tip: `d05afd1276` — includes `d8822a3e337` (Result/try-operator
  interpreter fixes), `86d48118a9f` (HIR aliases by physical source),
  `6b20d69a5cd` (module surface dict keys), and every seed fix listed in
  the pending set below.
- Recipe: `cargo build --profile bootstrap -p simple-driver --features llvm`
  (per `check-seed-native-build-invariant.shs`) in an isolated worktree
  with its own `CARGO_TARGET_DIR`.
- Binary: 154,094,616 bytes, sha256 `79ca755dd8e7dabf...`.
- Provenance vs deployed: all four marker rows PRESENT on both (JIT
  symbol manifest, JIT strict-mode knob, `.?` fix, LLVM codegen linked);
  `llvm::` symbol count 57,617 with `lld::=0`, i.e. real LLVM codegen.
- Build traps confirmed and avoided: plain `cargo build --release`
  produces a **no-LLVM** 57 MB binary that is NOT deploy-equivalent; and
  the `--features llvm` build was broken repo-wide by a private
  `process_c_runtime_arg_indices` (E0603) until `9b415cd50a3`.

## Fixes that go live on redeploy

`fbb00ce463c` pop/push allowlist · `ecc226b5136` interpreter byte-slice
indexing · `38cb691ad082` two-arg `index_of` · `7ce58e13952` optional
payload extraction · `e8e44f7bf9d` mixed-tuple element typing ·
`2f3de049661` negative single-index + double-print · `d8822a3e337`
Result/try-operator under interpret · plus this revision's
byte-transparent slices.

## Matrix — fresh candidate (PROVED, all runs on the candidate binary)

Acceptance gates:

| Gate | Deployed | Pre-fix candidate | Fresh candidate |
|---|---|---|---|
| json_unicode_escape (std) | 15/15 | **10/15** | **15/15** |
| json_unicode_escape (common/js) | 6/6 | **5/6** | **6/6** |
| json_unicode_escape (lib/js) | 10/10 | **7/10** | **10/10** |
| text_bracket_slice_byte_index | 2/14 | 14/14 | **14/14** |
| text_index_of_start | 9/21 | 21/21 | **21/21** |
| text_negative_single_index | 7/7 | 7/7 | 7/7 |
| result_interpret_lane | n/a | n/a | **11/11** |
| simple-parser crate (cargo test) | n/a | n/a | **895 passed, 0 failed** |

Byte indexing did NOT regress while byte transparency was restored —
that was the sharp edge of this fix and both halves hold.

Regression set (identical-or-better bar, all zero-failure):

| Suite | Fresh candidate |
|---|---|
| parsers_json_core | 94/94 |
| json_coverage | 187/187 |
| text_slice_substring | 76/76 |
| base58 | 18/18 |
| bencode multibyte / offset guard | 2/2, 6/6 |
| apply_decls_merge_probe | 20/20 |
| toml_multibyte | **3/3** (was 1/3 on deployed AND pre-fix candidate) |
| mqtt packet_negative_offset_guard | 1/1 |
| css_spec | 9/12 — the 3 reds are identical on the deployed binary (pre-existing, unrelated) |

Integration driver on the candidate: optional-tuple match binds `5 9`;
mixed tuple `M1: 7 IDX1: 7`; two-arg `index_of` returns `4` and `7`;
MQTT round-trip `DECODED: [café] CONSUMED: 7`.

`toml_multibyte` moving 1/3 -> 3/3 corrects the first pass's
"pre-existing red" classification: it was the same shred family as the
blocker, merely red on both binaries at the time.

## The fixed blocker (for the record)

Locus confirmed by reading the code: two `String::from_utf8_lossy` sites
in `compiler/src/interpreter/expr/collections.rs` (the range-index path
and the `Expr::Slice` path). Interpreter text is `Value::Str(Arc<String>)`,
so a mid-codepoint fragment cannot be held as a Rust `String`, and lossy
conversion destroyed the original byte before reassembly. Fix: a
`Value::StrBytes(Arc<Vec<u8>>)` variant used only for
not-yet-valid-UTF-8 fragments, `Value::text_from_bytes()` collapsing
back to `Str` as soon as bytes validate, and byte-transparent
concatenation / join / ordering / equality. Display and the FFI bridge
keep a lossy render — the only boundaries a fragment can escape through,
where lossy is correct. No `from_utf8_unchecked`; a corrupt `String`
can never reach display or FFI.

Diagnostic value of the canary: every pre-fix failure byte count matched
the 3-bytes-per-U+FFFD model exactly (canary 9 -> 27, emoji 4 -> 12,
round-trip 14 -> 32), which is what identified the mechanism before any
code was read.

## Deployment steps (NOT executed — user decision)

Never `cp` onto a live binary (Text file busy); use `.new` + `mv`. See
`doc/07_guide/app/mcp/mcp.md`.

```
# DEPLOY=<candidate binary>   (build with the canonical recipe above)
cp "$DEPLOY" bin/release/x86_64-unknown-linux-gnu/simple.new
mv bin/release/x86_64-unknown-linux-gnu/simple.new bin/release/x86_64-unknown-linux-gnu/simple
# .mcp.json launch path (gitignored), if present:
cp "$DEPLOY" bin/release/linux-x86_64/simple.new
mv bin/release/linux-x86_64/simple.new bin/release/linux-x86_64/simple
# then:
sh scripts/check/check-compiler-provenance.shs
```

Post-deploy re-verification (recorded repro drivers): the json escape
canary case, the optional-extraction repro, the mixed-tuple repros, and
the MQTT round-trip driver — see
`doc/08_tracking/bug/native_optional_tuple_payload_extraction_broken_2026-07-29.md`
and
`doc/08_tracking/bug/native_mixed_tuple_field1_statement_drop_2026-07-29.md`.
Re-run `bin/simple test` on the three json escape specs plus
`text_bracket_slice_byte_index` and `text_index_of_start` immediately
after deploying, since those five pin the interacting behaviors.

## PROVED vs INFERRED

PROVED: candidate identity and provenance parity; every table cell above
(direct execution on the candidate binary, outputs captured to files);
the blocker's locus (code read, two named conversion sites); the
CRLF/whole-file and no-LLVM build traps (observed, then avoided).
INFERRED: that no non-sampled suite regresses (the sample is the set this
session used as baselines plus the byte-index and Result lanes, not the
full suite); that display/FFI lossy rendering is acceptable for raw
fragments (design choice, matching the compiled lane's behavior at those
boundaries); that `css_spec`'s 3 reds are unrelated (identical on
deployed, root cause not investigated).
