# Seed redeploy readiness report — 2026-07-30

**Recommendation: NO-GO** — one blocking, candidate-only regression
(interpreter bracket slicing is byte-indexed but not byte-transparent:
mid-codepoint 1-unit slices normalize to U+FFFD, shredding raw non-ASCII
through every 1-unit-walk parser). Everything else on the
re-verification list PASSES, most dramatically better than deployed.
Fix the slice transparency, rebuild, re-run ONLY the json escape trio to
flip GO.

## Resolution (2026-07-30 update)

**The original NO-GO verdict is SUPERSEDED.** The blocking regression was
fixed in `8151c391932` ("fix(interpreter): byte-transparent text slices -
clears the sole redeploy blocker"), which introduced a
`Value::StrBytes(Arc<Vec<u8>>)` variant carrying raw bytes only when they
are not valid UTF-8 on their own, collapsing back to `Str` as soon as they
validate.

**PROVED:** a canonical seed was built with
`cargo build --profile bootstrap -p simple-driver --features llvm` and
**deployed** to `bin/release/x86_64-unknown-linux-gnu/simple`
(154,095,344 bytes, all 4 provenance markers present, `llvm::`=617,
`lld::`=0), with the previous binary retained as a named rollback. The
deployed binary then produced verified GREEN evidence for two showcase
cells the same day (`3b3fe52cbb7`, `4ab39e144de`).

**NOT VERIFIED HERE — do not read this section as claiming otherwise.**
This document does **not** record a post-fix re-run of the "json escape
trio" the GO criterion above names, nor of any broader test matrix. An
earlier revision of this section asserted both; that assertion was
unsupported and has been removed. The GO condition is met on the *deploy
and provenance* axis; anyone needing the trio-green evidence must run it
and record it here.

## Candidate identity (PROVED)

- Built from origin/main tip `dd7f9f1c975` in an isolated worktree.
- Canonical recipe: `cargo build --profile bootstrap -p simple-driver
  --features llvm` (per check-seed-native-build-invariant.shs).
- Binary: 154,084,544 bytes, sha256 `28e528ccd55d642d...`.
- Provenance marker rows match the deployed binary exactly (JIT symbol
  manifest, JIT strict-mode knob, `.?` fix, LLVM codegen linked — all
  PRESENT). Deployed for comparison: 145,448,208 bytes, sha256
  `e5c461a5f0cba9ba...`, same 4 markers.
- CAUTION for whoever rebuilds: a plain `cargo build --release` produces
  a NO-LLVM binary (57 MB, LLVM marker absent) — not deploy-equivalent.
- The `--features llvm` build was BROKEN at tip (E0603:
  `process_c_runtime_arg_indices` private, called from llvm-gated code;
  default-feature builds green so nothing caught it). Fixed in the same
  commit as this report (`pub(crate)` + comment). Any candidate built
  before that fix cannot exist.

## Delta note

Origin advanced during verification (tip at writing `ff785e9d8ca`,
including `7935e971737` fix(jit): preregister trait types). Those
commits are NOT in this candidate; re-verification of the failing trio
plus a spot-check is enough for a rebuilt candidate, not a full re-run.
The Result-under-interpret fix from another lane has NOT landed (no
matching commit at tip) — "unknown class Result" stays as-is either way.

## Matrix (candidate vs deployed, same worktree, same lanes)

Fix-goes-live items (all PROVED live on the candidate):

| Item | Deployed | Candidate |
|---|---|---|
| text_bracket_slice_byte_index_spec (interp) | 2/14 | **14/14** |
| text_index_of_start_spec (interp) | 9/21 | **21/21** |
| text_negative_single_index_spec (interp) | 7/7 | 7/7 |
| two-arg index_of driver (`abcabcabc`, start=2/5; miss; multibyte) | 27/27/27/27 (garbage) | **4 / 7 / neg-miss / 7** |
| optional payload repro (if-val Some, match tuple, i64?) | both-arms-skip / 3 3 / 3 | **x 7 / 5 9 / 41** |
| mixed-tuple repro (M1/SUM/IDX1) | dropped | **7 / 8 / 7** |
| boxed Some(99), homogeneous tuple, struct fields | ok | ok (byte-identical) |
| MQTT round-trip (native) | no decode | **DECODED café, CONSUMED 7** |

Regression sample (identical-or-better bar):

| Suite | Deployed | Candidate |
|---|---|---|
| parsers_json_core | 94/94 | 94/94 |
| json_coverage | 187/187 | 187/187 |
| text_slice_substring | n/a (not baselined) | 76/76 |
| base58 | n/a | 18/18 |
| bencode multibyte + offset guard | n/a | 2/2, 6/6 |
| apply_decls_merge_probe | n/a | 20/20 |
| css_spec | 9/12 | 9/12 (identical reds — pre-existing) |
| toml_value_guard | n/a | 5/5 |
| toml_multibyte | 1/3 | 1/3 (identical reds — pre-existing, NOT fixed by ecc226b5136; same shred family as the blocker but present on both) |
| mqtt packet_negative_offset_guard | 1/1 | 1/1 |

## THE BLOCKER (candidate-only regression, PROVED)

json_unicode_escape specs, green on deployed, red on candidate:
std 15/15 -> 10/15, common/js 6/6 -> 5/6, lib/js 10/10 -> 7/10.

The canary case built for exactly this fired: every failing byte count
matches the U+FFFD-per-fragment model exactly —

- canary "😀中é" (9 bytes) read back as 27 bytes = 9 fragments x 3-byte
  U+FFFD;
- raw "😀" 4 -> 12; mixed 14 -> 24; round-trip 14 -> 32.

Mechanism: under the candidate's byte-indexed interpreter slicing
(ecc226b5136), a 1-unit bracket slice mid-codepoint returns a 1-byte
invalid-UTF-8 fragment which the text layer normalizes to U+FFFD, so
fragment-wise reassembly (the json tokenizer's engine-agnostic 1-unit
walk, and any parser walking the same way) shreds all raw non-ASCII.
The compiled lane reassembles the same fragments byte-transparently
(bracket-slice survey), and the OLD interpreter returned whole
characters — both fine. The new interpreter is half-migrated:
byte-indexed but not byte-transparent. Required fix: byte slices of
text must preserve raw bytes so concatenation round-trips (match the
compiled lane), in ecc226b5136's slicing implementation. Then re-run
the three json escape specs + toml_multibyte (which may improve too).

## GO checklist and deployment steps (NOT executed — user decision)

Preconditions to flip GO:
1. Land the byte-transparency fix for interpreter bracket slices.
2. Rebuild candidate from the then-tip with the canonical recipe above.
3. Re-run: json escape trio (must be 15/15, 6/6, 10/10), the four
   drivers, bracket_slice/index_of_start pinning specs, toml_multibyte.

Deployment (the .new+mv dance; NEVER cp onto a live binary — Text file
busy; see doc/07_guide/app/mcp/mcp.md):

```
# from repo root, DEPLOY=<candidate binary path>
cp "$DEPLOY" bin/release/x86_64-unknown-linux-gnu/simple.new
mv bin/release/x86_64-unknown-linux-gnu/simple.new bin/release/x86_64-unknown-linux-gnu/simple
# .mcp.json launch path (gitignored) if present:
cp "$DEPLOY" bin/release/linux-x86_64/simple.new && mv bin/release/linux-x86_64/simple.new bin/release/linux-x86_64/simple
# verify:
sh scripts/check/check-compiler-provenance.shs
```

Post-deploy re-verification list (from standing memory): the json
escape canary, the optional-extraction repro, the mixed-tuple repros,
and the MQTT round-trip driver — all recorded in
doc/08_tracking/bug/native_optional_tuple_payload_extraction_broken_2026-07-29.md
and
doc/08_tracking/bug/native_mixed_tuple_field1_statement_drop_2026-07-29.md.

## PROVED vs INFERRED

PROVED: everything in the tables above (direct execution, outputs
captured); provenance marker parity; the llvm-feature build breakage
and its fix (build red -> green); the U+FFFD fragment arithmetic.
INFERRED: that the blocker's locus is ecc226b5136's slicing
implementation (from behavior + that commit's description; the code was
not bisected); that toml_multibyte would improve with the transparency
fix (same failure shape, unverified); native-lane results transfer from
the no-LLVM release binary to the bootstrap binary for JIT/interp code
paths (spot-confirmed on the json trio + toml + css, which matched).
