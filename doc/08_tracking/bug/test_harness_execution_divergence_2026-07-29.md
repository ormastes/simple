# `bin/simple test` gives wrong results for code that `bin/simple <file>.spl` computes correctly

**Status:** FIXED (2026-07-29, interpreter pass). The interpreter defect was
NOT recursion/branch-related: the tree-walking interpreter's bracket-slice
paths used a CHARACTER index space while the default engine (and the
interpreter's own index normalization) is BYTE-indexed.
`interpreter/expr/collections.rs` had two broken sites: the range-index
path (`s[a..b]`) computed indices against the character count and sliced a
char vector, and the `Expr::Slice` path (`s[a:b]`) normalized indices
against the BYTE length (`s.len()`) but then sliced a CHAR vector — an
internally mixed index space. Every byte-offset slice on multi-byte text
was silently wrong under `SIMPLE_EXECUTION_MODE=interpret`; the "minimal
isolate is correct" scoping below is explained exactly: the isolate did
only i64 arithmetic and never sliced text. Both sites now slice the byte
slice (U+FFFD substitution for a range that splits a codepoint —
byte-identical to native output when printed). Probes byte-identical across
engines after the fix (glob true, "日本語"[3:6]=="本",
"caféZdef"[-3:]=="def"); regression spec
`test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl` runs under the
forced-interpret test lane.

**Adjacent divergences, close-out pass (2026-07-29, same session):**

- **`v[-2]` single-index — FIXED (JIT lane).** Text single-indexing is
  CHARACTER-indexed (family rule: `s[i]`/`char_at`/`char_code_at` keep
  character semantics; slices/len/index_of are byte-indexed), and the
  reference doc documents negative indexing for the sequence family. The
  JIT lane's `rt_string_char_at` (Rust runtime crate) returned NIL for any
  negative index, so `"aé🙂z"[-2]` was nil under the default engine while
  the interpreter returned "🙂". Negative indices now resolve against the
  character count, Python-style. DECISION: interp semantics were correct;
  native was fixed.

- **Interpreter double-print of module-level `main()` — FIXED.** The
  interpreter executed a top-level `main()` statement AND then
  unconditionally auto-called `main` as the entry point; the default
  engine runs such scripts once (proved by a 3-probe matrix: auto-call
  exists in both engines, top-level statements run in both, but the
  default engine suppresses the auto-call when the script itself calls
  `main()`). The interpreter now records a direct top-level `main()` call
  and suppresses the automatic entry call.

- **Negative-step text slices (`s[::-1]`) — DEFERRED, decision needed.**
  The reference doc documents `[::-1]` for LISTS only; for text the
  engines disagree: native `rt_slice` returns "" for any negative stride
  (its string loop only iterates forward), while the interpreter
  byte-steps Python-style (which corrupts multi-byte text in either unit).
  PROPOSAL (least surprising): make a negative-step TEXT slice an ERROR in
  both engines and point users at `.reversed()` (character-aware); byte
  reversal is never meaningful for UTF-8 and silent "" is astonishing.
  Not changed unilaterally — flagged for decision.

- **`rt_string_char_at` three-way unit divergence — DEFERRED, decision
  needed.** The Rust runtime impl is CHARACTER-indexed; the C
  `runtime_native.c` impl and the pure-Simple
  `simple_core/core_string.spl` impl return the single BYTE at the index
  (the .spl one explicitly documents the divergence, without rationale).
  So AOT-linked and self-hosted binaries disagree with the JIT lane and
  the interpreter on `s[i]`/`char_at` for multi-byte text TODAY. Aligning
  them to character semantics is the family-consistent fix but needs a
  self-hosted impact pass first: self-hosted internals were built against
  byte-at behavior, and codepoint-seeking makes every `s[i]` walk O(n^2)
  (lexer-shaped risk; see the char_code_at O(i) family). Flagged, not
  changed. IMPACT PASS COMPLETED — see the decision brief below.

## Decision brief: `s[i]` / `char_at` unit alignment (2026-07-29 impact pass; NO semantics changed)

### Empirical behavior matrix (probe string "aé🙂z")

| Lane | Binary measured | Unit | Negative index | Status |
|---|---|---|---|---|
| Seed default (JIT; Rust runtime crate) | deployed `bin/simple` | CHARACTER (`v[1]`=="é", `v[2]`=="🙂", char_code_at(1)==233) | nil before 2f3de049661, char-from-end after | PROVED |
| Seed forced interpret | same binary, SIMPLE_EXECUTION_MODE=interpret | CHARACTER (same outputs) | char-from-end | PROVED |
| AOT / C runtime (`runtime_native.c`) | direct C harness linked against runtime_native.c + runtime.c + runtime_legacy_core.c: `rt_string_len(rt_string_char_at(v, 1))`==1 (one byte, half of é), `(v, 2)`==1, `(v, -2)`→nil | BYTE | nil | PROVED (upgraded from source reading) |
| Self-hosted (`simple_core/core_string.spl`) | not runnable this pass: stage3 binary was deleted by a parallel session mid-probe, stage2 is compile-only ("unknown command 'run'"), and the native-build worker lane fails (pre-existing) | BYTE | nil | INFERRED (source + its own explicit "byte-indexed" doc comment) |

### Blast radius (owned, non-test)

- `.char_at(` sites: src/lib 868, src/app 203, src/os 70, src/compiler 33
  — 1,174 total (plus 281 in test/). Same-family `.char_code_at(`:
  src/lib 225, src/app 60, src/compiler 12.
- Dual-lane exposure is STRUCTURAL, not a subset: the same `.spl` source
  runs under seed tools (character lanes) and inside self-hosted / AOT /
  SimpleOS artifacts (byte lanes). Every site whose receiver can carry
  non-ASCII behaves differently per lane today.
- Concrete dual-lane scan sites (from a random 14-site sample):
  `src/lib/editor/view/md_editing.spl` (`while i < line.len() and
  line.char_at(i) == " "`), `src/lib/editor/services/diagnostics.spl`
  (json scans), `src/lib/common/markdown_visual_editor.spl`,
  `src/lib/nogc_sync_mut/db/dbfs_engine/sql_parser.spl`,
  `src/app/devhub/cmd_email.spl`,
  `src/compiler/70.backend/linker/linker_script.spl` — all drive
  `char_at(i)` from a BYTE-valued `.len()` bound.
- Index-derivation profile: of 1,104 sites in src/{lib,compiler,app},
  180 have `.len()` on the same line (the byte-derived loop-bound form)
  and 67 are `char_at(0)`; the random sample classifies ~10/14 as
  byte-derived scans and ~2/14 as ASCII-protocol first-char checks
  (unit-agnostic). The corpus is overwhelmingly written AS IF `char_at`
  were byte-at.

### Cost model

**Option A — align C + simple_core impls to CHARACTER (documented family rule):**
- Correctness: matches the docs, both seed lanes, the landed
  negative-index fix, and `text_negative_single_index_spec`. Zero
  tool-lane behavior change.
- Perf: `rt_string_char_at` goes O(1)→O(i) in self-hosted/AOT. The
  feared O(n^2) LEXER regression is REFUTED: the pure-Simple lexer's
  hot path reads characters via `source[pos:pos + 1]` byte
  bracket-slices (`lex_source_char_at`, lexer.spl:200) and its
  single-index uses are on array slots — zero `char_at`/`char_code_at`
  in the scan loop. The byte-derived `while i < s.len(): s.char_at(i)`
  scan sites above DO become O(n^2) under self-hosted/AOT — the same
  cost those loops already pay in the seed tool lanes today (the Rust
  impl is `chars().nth`, O(i)).
- Migration: no call-site edits strictly required; multibyte behavior
  of the byte-derived scans under self-hosted/AOT changes to match what
  the tool lanes already do.

**Option B — align Rust runtime + seed interpreter to BYTE (matches how the corpus is written):**
- Correctness: byte-derived scans become self-consistent in ALL lanes
  and O(1); genuinely char-reliant sites break on multibyte (rare in
  the sample; protocol code is ASCII-safe either way).
- Contradicts: the documented character-semantics family rule,
  `char_code_at`'s UTF-8 decoding, the just-landed negative-index fix
  and its spec, and the `value_tests_basic` single-index clauses — all
  would need re-pinning; `char_code_at` needs the same decision or the
  family splits internally.
- Perf: all lanes O(1).

**RECOMMENDATION: Option A** (align the byte-at impls to character),
because (1) it is the documented family rule, (2) the lexer-perf
objection is empirically refuted, (3) tool-lane behavior — what tests
and users actually see — is already character and freshly spec-pinned,
and (4) Option B silently changes multibyte behavior of the two lanes
people interact with daily. Separately, the byte-derived
`.len()`-bounded `char_at(i)` scan family is wrong in the tool lanes
TODAY under either option (byte bound driving a char index — the
byte-vs-character bug family again) and should migrate to byte
bracket-slices (`s[i:i + 1]`) opportunistically. USER DECIDES; nothing
changed in this pass.

## Byte-bounded char_at scan migration — campaign CLOSED (2026-07-30)

Four batches migrated every high-exposure `.len()`-bounded char_at scan
to byte bracket-slices, with the SPAN-APPEND RULE (mandatory since
batch 2) for accumulation loops: byte-slice COMPARES are safe, but
APPENDS must flush whole spans between ASCII boundaries — the
interpreter's Rust-String values turn a mid-codepoint 1-byte slice into
U+FFFD (PROVED: per-byte accumulation of a 12-byte multi-byte string
yields 36 bytes under the interpreter, exact 12 under JIT/native).

| Batch | Commit | Files | char_at sites | Notes |
|---|---|---|---|---|
| 1 | f8595a57cd9 | md_editing, diagnostics, markdown_visual_editor, sql_parser, cmd_email, linker_script | 70 | shape probe old-wrong/new-right, ASCII pinned |
| 2 | 2d70e40905f | lsp_result_panel, md_lsp_handler, json/parser, md_doc_stats, completion (+ span hardening of batch-1 diagnostics, sql_parser) | 45 | span rule discovered via json_unicode_escape_spec regression; failing set restored to pristine's 5 pre-existing |
| 3 | 38eab98f352 | mcp/resource_utils, dap_protocol, gui_backend, editor_json_helpers, formula, md_wiki_index, md_language, md_renderer, editor_markdown_helpers | 142 | escape round-trip probe byte-identical both engines |
| 4 | (this commit) | browser renderer core, debug_session_registry, md_search, md_diagnostics, document, block_model | 100 | label/url/alt extraction span-hardened |

Same-line `.len()`-bounded site count: ~180 at survey -> 166 -> 121 ->
61 -> ~36 after batch 4.

STOP RULE: the remaining tail is ASCII-protocol scanners where the unit
provably never matters (lsp_transport framing headers, llm_runtime API
probes, hex/digit scanners) plus 1-2-site stragglers. These are handled
by (a) the pending char_at unit-alignment decision above and (b) the
documented span/byte-slice rule applied opportunistically when a file
is touched. No further dedicated batches.

POST-SEED-REDEPLOY RE-VERIFICATION: the probes in this campaign ran on
tip-built seeds; after the next seed/self-hosted redeploy, re-run
test/01_unit/bugs/text_bracket_slice_byte_index_spec.spl,
text_negative_single_index_spec.spl, text_index_of_start_spec.spl and
test/01_unit/lib/common/json/json_unicode_escape_spec.spl under
bin/simple test (forced-interpret lane) — they pin every semantics this
campaign relies on. The 5 json_unicode_escape reds that predate the
campaign remain open (interp-lane byte-exactness, tracked separately).

Historical report below (pre-fix):

**Status (superseded):** ROOT-CAUSED (2026-07-29, follow-up pass). **Severity:** every
`bin/simple test` run executes specs under the buggy engine unconditionally
— any spec whose code shape matches this bug's trigger (below) reds
regardless of whether the code under test is correct. **Not fixed** — an
interpreter-evaluation bug is out of scope for this pass; documenting
precisely per instruction, not attempting a codegen/interpreter fix.

## Root cause (PROVED, not inferred)

`bin/simple test`'s per-spec child process
(`src/app/test_runner_new/test_runner_single.spl:330-331`,
`fn main() -> i64`) unconditionally sets, before running the spec's actual
code:
```
rt_env_set("SIMPLE_RUNTIME_MODE", "interpreter")
rt_env_set("SIMPLE_EXECUTION_MODE", "interpret")
```
This forces the tree-walking **interpreter** engine for every spec run,
regardless of what `bin/simple <file>.spl` would default to on its own.

**Discriminating experiment** (same file, same path, zero test-runner
machinery involved — a plain script, run two ways):
```
$ bin/simple probe.spl                                  # default engine
RESULT=true                                              # correct

$ SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl   # forced interpreter
RESULT=false                                             # WRONG
RESULT=false                                             # (printed twice — see "Also observed" below)

$ SIMPLE_RUNTIME_MODE=interpreter bin/simple probe.spl   # the OTHER var alone
RESULT=true                                               # correct — NOT the trigger
```
`SIMPLE_EXECUTION_MODE=interpret` alone reproduces the wrong result;
`SIMPLE_RUNTIME_MODE=interpreter` alone does not. The test harness sets
both, but **`SIMPLE_EXECUTION_MODE=interpret` is the specific trigger**.

This directly reproduces the exact `bin/simple test` failure using nothing
but an env var on a plain script — conclusively locating the divergence in
the **execution engine** (default/JIT-or-native vs. forced interpreter),
not in the test harness's path resolution, caching, or spec-block
semantics.

## Investigation-guide checklist (all 4 hypotheses tested)

- **(a) test-path/module resolution divergence:** RULED OUT. Reproduced
  with a plain script at a path with zero test-runner involvement — same
  file, same `use` import, no `test/` directory, no spec framework.
- **(b) different execution engine:** CONFIRMED — this is the root cause.
  Correction to the guide's framing: it is **not** "test lane JITs where
  direct interprets" — empirically it's the reverse. Default execution
  (what `bin/simple file.spl` uses with no env override) is correct;
  forced **interpreter** mode (what the test harness always sets) is
  **wrong**. The guide's suggested "known call-boundary miscompile family"
  connection is directionally right (an engine evaluates a call-derived
  value incorrectly) but the specific broken engine is the interpreter,
  not JIT/native.
- **(c) stale `.smf` cache shadowing:** RULED OUT. Fresh worktree, `find
  <worktree> -iname '*.smf'` → 0 results before any run; no
  `.simple/`/`~/.simple` cache directory exists in this environment at
  all. Nothing to shadow.
- **(d) test-runner spec-harness semantics (it-block/return quirks):**
  RULED OUT. Reproduced with a plain `fn main(): print(...)` script — no
  `describe`/`it`/`expect`, no spec harness of any kind involved.

## Scoping: NOT simply "any call-derived local threaded into a recursive argument"

A minimal isolate with the *same shape* (extract a helper-call result to a
local, add it to an index, pass the result as a named argument to a
recursive call) evaluates **correctly under forced interpreter mode**,
even at recursion depth 5:
```
fn codepoint_len(s: text, si: i64) -> i64: ...        # same helper shape
fn recursive_probe(s: text, si: i64, depth: i64) -> i64:
    if depth <= 0: return si
    val step = codepoint_len(s, si)
    val next_si = si + step
    recursive_probe(s: s, si: next_si, depth: depth - 1)
# SIMPLE_EXECUTION_MODE=interpret: correct at depth 1 AND depth 5
```
So the bug needs more of `_glob_at`'s real shape to manifest — most likely
its **multiple early-return branches** (`*`/`?`/`[`/literal-match/`false`
all coexisting in one function with several `if ... return` guards ahead of
the recursive call) and/or genuine multi-step pattern-matching recursion
(not just repeated identical steps) — not merely "a call result in a
recursive argument position." Not narrowed further than this; a full
interpreter-internals investigation is out of scope for this pass per
instruction.

## Also reproduces in `src/lib/common/js/builtins/string.spl` (confirms it's not glob-specific)

```
$ bin/simple probe.spl                                       # default
charAt1=本                                                    # correct

$ SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl        # forced interpreter
charAt1=                                                       # WRONG (empty)
charAt1=                                                       # (printed twice, same as glob)
```
Same `string_charAt`/`text_codepoints`/`utf8_codepoint_byte_len`-walking
loop as documented in the bracket-slice fix pass. Same trigger
(`SIMPLE_EXECUTION_MODE=interpret`), same engine, confirming this is a
general interpreter-engine defect for this code shape, not something
specific to `glob.spl`'s recursion.

## Also observed, not investigated further (tangential)

Under forced interpreter mode only, both repro scripts above print their
`RESULT=`/`charAt1=` line **twice** for one `main()` call and one explicit
`main()` invocation at module scope. Not seen under default execution.
Could be an unrelated "module top-level re-executed" interpreter quirk, or
could be mechanically related to the same root cause (e.g. a retry-on-
wrong-result path). Not chased down — flagging in case it helps whoever
investigates the interpreter bug itself.

## What this is NOT

- Not a logic bug in the bracket-slice fixes (`1bd388912f5`) — proved by
  default-engine execution producing correct output for every case the
  forced-interpreter path gets wrong, same source, same session.
- Not the previously-fixed for-loop-over-text corruption
  (`doc/08_tracking/bug/for_loop_over_text_char_code_at_zero_len_crash_2026-07-19.md`)
  — neither fixed function uses `for x in text:`.
- Not literally the tuple/aggregate-return corruption class
  (`doc/08_tracking/bug/native_tuple_spill_clobber_across_call_2026-07-19.md`)
  — that family is about **native/codegen** aggregate returns; this bug is
  in the **interpreter**, triggers with plain scalar (`i64`) locals (no
  tuples anywhere in the final `glob.spl`/`string.spl` source), and needs
  multi-branch recursion to manifest (see Scoping above) where that family
  needed only a single intervening call. Related in spirit (an execution
  engine mishandles a value threaded through locals across a call
  boundary) but a distinct instance — do not merge these into one bug.
- Not path resolution, not `.smf` caching, not spec-harness semantics —
  all three directly ruled out above.

## Impact

Every `bin/simple test` run forces `SIMPLE_EXECUTION_MODE=interpret` for
every spec, unconditionally (`test_runner_single.spl:330-331`, no opt-out
flag found in that file). Any spec exercising code with this bug's trigger
shape reds regardless of whether the code under test is correct — this
poisons `bin/simple test` as a verification source for that code shape
specifically, not just for the two files in this session's fix. The
`string.spl`/`glob.spl` fixes from `1bd388912f5` remain landed; re-verify
them via default-engine execution (see Reproduce) until the interpreter bug
itself is fixed, not via `bin/simple test`.

## Reproduce

```
cd <fresh worktree, built bin/simple symlink>

cat > probe.spl <<'EOF'
use std.nogc_sync_mut.glob.{glob_match}
fn main():
    print("RESULT={glob_match(\"café.txt\", \"caf?.txt\")}")
main()
EOF

bin/simple probe.spl                                # RESULT=true (correct)
SIMPLE_EXECUTION_MODE=interpret bin/simple probe.spl # RESULT=false (WRONG)
SIMPLE_RUNTIME_MODE=interpreter bin/simple probe.spl # RESULT=true (correct -- isolates the trigger var)
```
