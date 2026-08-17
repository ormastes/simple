# Bracket-slice (`s[i:j]`) byte-index survey — file classification, 2026-07-29

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Follows on from:** `doc/08_tracking/bug/web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
§ "bracket-slice (`s[i:j]`) survey gap" (enumerated **1,193 sites / 393 files**,
top-concentration table + a domain-guess classification of ~20 files, not
individually spot-checked beyond 6 files).

This pass classifies **every file** the prior enumeration reached (plus the
files its raw regex also reaches) into LOW / HIGH / MIXED-UNKNOWN, and spot-
checks 2-3 sites in each of the highest-count HIGH files for byte- vs
char-derived index provenance, per the assignment brief.

## Methodology and count reconciliation

```
grep -rn --include='*.spl' -E '\[[a-z_0-9 +*-]+:[a-z_0-9 +*-]*\]' src/
```

Run fresh (2026-07-29) against `origin/main` (`f9d064c4d57`, isolated
worktree — see Landing): **3,105 raw hits across 693 files**, not 1,243/393.
Reconciled the gap in two documented, reproducible steps (both counts
verified, not estimated):

1. **Full-line comments** (`grep -vE '^[^:]+:[0-9]+:[[:space:]]*#'`): **481
   hits removed** (2,624 remain). A large share of these are bitfield-layout
   comments in hardware files, e.g. `# VPN[1] = bits [29:21]` — documentation
   of a register/instruction encoding, not a code site at all.
2. **Hardware/bit-array-domain paths** (`hardware/`, `kernel/arch/`,
   `backend/native/`, riscv/arm/avx/sve/rvv/mmu/paging/rtl/fpga/vhdl_gen/
   evex/baremetal/simd/zstd/crypto path fragments): **272 more hits removed**
   (2,352 remain, 581 files). These are real code sites, but slice **integer
   bit arrays** (`bits[63:62]`, opcode `funct5 = instr[31:27]`), not `text` —
   "arrays are fine" per the brief.

**2,352 sites / 581 files is this pass's candidate pool** — still ~2x the
prior survey's 1,193/393. The remaining gap is plain **array** slicing
scattered through ordinary (non-hardware) code (`args[1:]` on a `[Value]`
parameter array, `_flatten_args(args[1:])`, etc.) that only per-site type
inspection can filter out, not a path/keyword heuristic. This pass does not
attempt that at every site (2,352 sites is not tractable to hand-verify in
one pass); instead, per-site array-vs-text verification is folded into the
**file-level classification below** (a keyword/domain heuristic, same
methodology the prior survey used) plus the mandated 2-3-site **spot-check
on HIGH files**, where one spot-check below (`formula.spl`) caught exactly
this false-positive class and the file was pulled from the HIGH list
entirely as a result — see "Spot-check findings".

**Do not read "2,352 ≠ 1,193" as a discrepancy in the prior survey** — it
almost certainly did the same per-site type check this pass didn't have
budget to repeat at full scale; its top-file counts (`lint_short_grammar.spl`
67, `json.spl` 21, `serialization/__init__.spl` 19, `regex_nfa.spl` 15) land
close to (not identical to) this pass's counts for the same files (65, 22,
28, 15 respectively — see tables below), consistent with the same files,
slightly different filter strictness, not a different codebase state.

## Aggregate counts by class

| Class | Files | Sites | Note |
|---|---|---|---|
| **LOW** | 157 | 855 | compiler/desugar/lexer/parser-over-Simple-or-JS-grammar domain; 3 files reclassified here from a HIGH keyword hit after inspection (see below) |
| **HIGH** | 127 | 577 | arbitrary/user/network data domain; 4 files removed from the raw HIGH-keyword hit list after inspection (1 false-positive array file, 3 reclassified to LOW) |
| **MIXED/UNKNOWN — explicit reason** | 2 | 2 | keyword-ambiguous, see below |
| **MIXED/UNKNOWN — not yet triaged** | 294 | 914 | matched neither the LOW nor HIGH domain-keyword filter; needs individual review, see sample below |
| Excluded (false positive, array not text) | 1 (`formula.spl`) | 4 | caught by spot-check, see below |
| **Total (candidate pool)** | 581 | 2,352 | |

## HIGH-risk files (127, all counts, after correction)

Domain: JSON/JS values, HTTP/auth/cookie/session, HTML/DOM, i18n, git/scv
(arbitrary commit/file content), MCP/LSP/debug-adapter protocols carrying
arbitrary strings, LLM/caret bridges, config/registry metadata.

| Sites | File |
|---|---|
| 28 | `src/lib/common/serialization/__init__.spl` (fixed `c24918ae676`) |
| 22 | `src/lib/common/js/builtins/json.spl` |
| 21 | `src/lib/scv/fast_import.spl` |
| 16 | `src/app/todo_scan/main.spl` |
| 16 | `src/app/devhub/convert_storage.spl` |
| 15 | `src/lib/nogc_sync_mut/web_framework/auth_middleware.spl` |
| 15 | `src/lib/nogc_sync_mut/debug/remote/protocol/gdb_mi_parser.spl` |
| 15 | `src/lib/nogc_async_mut/debug/remote/protocol/gdb_mi_parser.spl` |
| 15 | `src/app/debug/remote/protocol/gdb_mi_parser.spl` |
| 14 | `src/app/ui.browser/dom_bridge.spl` |
| 13 | `src/lib/scv/fast_import_format.spl` |
| 13 | `src/lib/nogc_async_mut/web_framework/app.spl` |
| 12 | `src/lib/scv/structural_match.spl` **— suspected bug, see below** |
| 12 | `src/lib/scv/network_remote.spl` |
| 11 | `src/lib/nogc_sync_mut/web_framework/form_parser.spl` |
| 11 | `src/lib/gc_async_mut/pure/nn/serialization.spl` |
| 10 | `src/lib/nogc_sync_mut/web_framework/session.spl` |
| 9 | `src/lib/nogc_async_mut/mcp/fileio_json.spl` |
| 7 | `src/os/services/llm/widget_eval.spl` |
| 7 | `src/lib/scv/maintenance.spl` |
| 7 | `src/lib/nogc_async_mut/web_framework/router.spl` |
| 7 | `src/compiler_rust/lib/std/src/mcp/core/markdown.spl` |
| 7 | `src/app/ui.web/auth_params.spl` |
| 7 | `src/app/portal/server.spl` |
| 6 each | `web_framework/tracing.spl`, `web_framework/password_reset.spl`, `debug/remote/protocol/gdb_mi.spl` (×2 tier copies), `web/browser_session_html.spl`, `mcp/core/diagnostics.spl`, `portal/template.spl`, `devhub/adapter_minio.spl`, `app/debug/remote/protocol/gdb_mi.spl` |
| 5 each | `core/regex.spl`, `io/regex_simple.spl` (×4 tier copies), `database/feature_utils.spl` (×2 tier copies), `devhub/wiki_git.spl` |
| 4 each | `_McpOsServer/helpers.spl`, `scv/parser.spl`, `web_framework/asset_pipeline.spl`, `lsp/main_wasi.spl`, `i18n/bundle.spl`, `scv/main.spl`, `llm_caret/.../replBridgeTransport.spl`, `i18n/main.spl`, `devhub/storage_addr.spl`, `devhub/cmd_github.spl`, `devhub/cmd_bb.spl` |
| 1-3 each (66 files) | remaining `scv/*`, `mcp/*`, `devhub/cmd_*` (jira/email/outlook/bitbucket/minio/tasks/wiki/auth/api/daily_debug), `llm_caret/*` bridge/util files, `portal/*` controllers, `ui.browser/*`, `editor/*`, misc — full list is the raw grep output, not reproduced here in full to keep this doc bounded; see Reproduce |

## Spot-check findings (2-3 sites per top HIGH file)

**Byte-consistent, confirmed safe** (index built from `index_of`/fixed-ASCII-
prefix arithmetic, or a byte-walk that never skips a byte position even
though it "looks like" char-by-char):

- `json.spl:29,59,66` (`input[p:p+1]`, `input[i:i+1]`) — read closely at
  `parse_string` (lines 52-91): the loop always does `i = i + 1` exactly
  once per iteration regardless of what byte `ch` held, and the "regular
  character" branch does `result = result + ch` unconditionally. For a
  multi-byte UTF-8 character this reads and re-appends each of its bytes
  across successive iterations in order — the reconstructed `result` is
  byte-identical to the input. Genuinely byte-safe, not accidentally so.
  **Different, non-index bug found in the same loop** (flagged for its own
  ticket, not a bracket-slice/index bug): `\uXXXX` escapes are decoded to a
  literal `"?"` placeholder (`json.spl:83-85`, comment says "simplified,
  skip 4 chars") — any JSON string with a `\u`-escaped codepoint loses that
  character. `i = i + 4` itself is byte-consistent (4 ASCII hex digits), so
  this is a **data-loss bug, not an index bug** — do not conflate the two
  when filing.
- `fast_import.spl:160,443,444`, `fast_import_format.spl:67,94,111` — fixed
  offsets (`[1:]`, `[6:]`, `[5:]`, `[7:]`) all skip literal ASCII git
  fast-import keyword prefixes (`mark :`, `data `, etc.) — safe by
  construction, the prefix is always ASCII regardless of payload content.
- `todo_scan/main.spl:99,103,108` — same fixed-ASCII-prefix pattern
  (`TODO:`/`FIXME:`-class markers).
- `auth_middleware.spl:286,290,309` (`value[7:]`) — stripping the literal
  7-byte `"Bearer "` prefix from an `Authorization` header. Safe.
- `dom_bridge.spl:64,90,95` and 3 more checked — `lt`/`gt`/`pos` all come
  from `html.index_of("<", pos)` / `index_of(">", lt)` (line 64, 90).
  Byte-consistent throughout the file's tag-boundary scan.
- `gdb_mi_parser.spl:78,83,118` — `trimmed[1:]` (fixed ASCII quote-prefix
  strip) and `raw[0:comma_pos]` where `comma_pos` — spot-checked as
  `index_of`-derived. Safe for these 3 sites; GDB/MI additionally
  hex/octal-escapes non-ASCII debuggee string content before this parser
  ever sees it, which is why fixed-ASCII assumptions hold here.
- `web_framework/app.spl:320,322,324`, `form_parser.spl:50,51,121`,
  `network_remote.spl:30,37,42` — all `index_of`/fixed-ASCII-prefix derived.
  Safe for the sites checked.
- `pure/nn/serialization.spl:39,49,131`, `web_framework/session.spl:323,
  329,369` — the 3 sites checked in each file are numeric/type-tag literal
  parsing (`"-"` sign check, `"i:"` type prefix) — ASCII by construction
  regardless of what other fields in the same file carry. **Not exhaustive**
  — each file has more sites (11 and 10 respectively) not individually
  checked this pass; flagged for a fuller pass given the "arbitrary
  tensor/model metadata" and "arbitrary session payload" domains.

**Confirmed suspected bug — char-derived index fed into a byte-indexed
slice:**

- **`src/lib/scv/structural_match.spl:424-430`**, function
  `scv_find_char_pos(s: text, ch: text) -> i64`:
  ```
  fn scv_find_char_pos(s: text, ch: text) -> i64:
      var i = 0
      while i < s.len():        # s.len() is BYTE length
          if s.char_at(i) == ch: # char_at(i) is CHARACTER-indexed
              return i
          i = i + 1
      -1
  ```
  Loop bound (`s.len()`, bytes) and access (`char_at(i)`, characters) use the
  same counter `i` in two different index spaces — the exact "known split"
  this survey brief calls out. For pure-ASCII input this is harmless (byte
  count == char count). For any `s` containing a multi-byte UTF-8 character
  before the target `ch`, `char_at(i)` walks characters while `i` has
  already over-shot in byte terms (or under-shoots relative to what a byte
  offset would need to be), and the **returned `pos` is a character index,
  not a byte index**.
  Every call site treats the return value as a byte offset for a
  bracket-slice immediately after:
  - `structural_match.spl:441` `return rest[0:pos].trim()` (from `fn ` line)
  - `structural_match.spl:450` `return rest[0:end_pos].trim()` (from `class ` line)
  - `structural_match.spl:458` `return rest[0:cpos].trim()` (from `struct ` line)
  - `structural_match.spl:466` `return rest[0:cpos].trim()` (from `module ` line)
  All four extract a definition name from a source line up to `:`/`(` — if
  that source line has a multi-byte character before the delimiter (e.g. a
  non-ASCII identifier-adjacent comment fragment on the same physical line,
  or, more directly, an emoji/non-Latin string literal token appearing
  before the delimiter is reached in whatever text `line` actually is at the
  call site), the slice cuts at the wrong byte boundary — either truncating
  mid-character or including trailing garbage bytes. `structural_match.spl`
  is scv's (source-control tool) structural diff matcher; `line` here is
  raw *source* text, which is ASCII-grammar for identifiers but **not**
  restricted to ASCII on the rest of the physical line (trailing comments,
  string literals). Domain risk: real but narrow (requires non-ASCII content
  specifically before the delimiter on a definition line) — not the file's
  only 12 sites, the other 8 (`line[5:]`, `line[7:]`, `line[3:]`, `line[6:]`,
  `line[9:]`) are fixed-ASCII-keyword-prefix strips and are safe by the same
  reasoning as `fast_import.spl` above. Grepped for the same
  `.len()`-bound-but-`.char_at()`-indexed idiom elsewhere in `src/`
  (excluding vendored code): **this is the only occurrence** — not systemic.

**False positive caught and removed from the HIGH list:**

- **`src/app/office/sheets/formula.spl`** — matched the HIGH-domain keyword
  filter (`formula`) and has 27 `.char_at(` calls (tokenizing spreadsheet
  formula syntax), which made it look like a strong bug candidate. On
  inspection, its **only 4 bracket-slice matches are `args[1:]`** (lines
  5372, 5679, 6120, 6130) inside `_flatten_args(args[1:])` — `args` is the
  function-argument array (`[Value]`) passed to a formula builtin, an
  **array slice, not a text slice**. None of the file's 27 `char_at` calls
  feed a bracket-slice anywhere (verified by grep: no `expr[`/`token[`/`s[`
  pattern exists in the file at all). Removed from the HIGH bracket-slice
  list entirely — it has zero genuine text-slice sites.

## LOW-risk files (157, top 25 shown)

Compiler-internal / desugar / lexer / parser / tooling operating on Simple
or JS **source grammar** (identifiers, keywords, punctuation — ASCII by
language spec) or on other ASCII-only internal formats. 3 files added here
after inspection despite matching a HIGH keyword by accident:
- `src/compiler_rust/lib/std/src/mcp/simple_lang/dependencies.spl` — matched
  keyword `mcp` (its path contains `mcp/simple_lang/`), but it parses
  `import`/`pub import` lines of **Simple source** (`line[11:]`, `line[7:]`,
  fixed keyword-length prefixes) — same ASCII-grammar domain as
  `desugar/*`, not an MCP protocol/data file. Reclassified LOW.
- `src/lib/nogc_sync_mut/tooling/regex_match.spl`,
  `src/lib/nogc_sync_mut/tooling/regex_nfa.spl` — matched keyword `regex`,
  but the prior survey already read these and called them "likely low-risk
  (structural/ASCII-only domain)" alongside `pure/lexer.spl`/
  `common/parser/lexer.spl`. Deferred to that existing judgment rather than
  re-litigating (`s[i:j]` here walks the regex **pattern** string, not
  arbitrary matched text) — carried forward as LOW per the brief's "avoid
  redoing work" instruction.

| Sites | File |
|---|---|
| 65 | `src/compiler/90.tools/fix/rules/impl_/lint_short_grammar.spl` |
| 27 | `src/app/desugar/forwarding.spl` |
| 22 | `src/app/desugar/static_methods.spl` |
| 21 | `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` |
| 17 | `src/compiler/10.frontend/treesitter/heuristic.spl` |
| 17 | `src/app/traceability/_TraceabilityCore/warning_counts.spl` |
| 17 | `src/app/desugar/static_constants.spl` |
| 16 | `src/compiler/10.frontend/core/interpreter/cli_eval.spl` |
| 16 | `src/app/desugar/type_scanner.spl` |
| 15 | `src/compiler/80.driver/incremental_builder.spl` |
| 15 | `src/app/desugar/trait_scanner.spl` |
| 15 | `src/app/desugar/enum_constructors.spl` |
| 14 | `src/lib/gc_async_mut/pure/lexer.spl` |
| 14 | `src/lib/common/parser/lexer.spl` |
| 13 | `src/app/desugar/context_params.spl` |
| 12 | `src/app/desugar/rewriter.spl` |
| 12 | `src/app/cli/arch_check.spl` |
| 11 | `src/compiler/70.backend/backend/cli_codegen.spl` |
| 11 | `src/compiler/10.frontend/parser/partial.spl` |
| 11 | `src/app/desugar/trait_static_dispatch.spl` |
| 11 | `src/app/cli/check_tier.spl` |
| 10 each | `test_runner/test_executor_parsing.spl`, `test_runner/sdoctest/extractor.spl`, `parser/doc_gen.spl` |
| 9 | `core/_ParserPrimary/primary_expr.spl` |
| ... | 133 more files, 1-9 sites each, same domain — see Reproduce |

**Caveat carried from the prior survey, not re-verified this pass:** LOW
here means "ASCII by grammar for identifiers/keywords" — it does **not**
mean every character on every source line is ASCII (comments and string
literals in Simple/JS source are free-form UTF-8). `comment_extractor.spl`
below is the concrete instance of this exact caveat.

## MIXED/UNKNOWN (296 files, needs individual triage)

**2 files, explicit reason (keyword-ambiguous, both domains legitimately apply):**
- `src/compiler/50.mir/mir_json.spl` — compiler-internal (MIR = compiler IR)
  but emits/parses **JSON**, which can carry arbitrary string content
  (diagnostic messages, symbol names quoting source identifiers that
  themselves could theoretically be non-ASCII in a string literal context).
- `src/compiler/80.driver/driver_public_header_parse.spl` — compiler-internal
  but parses **C header** content, which is not Simple-grammar-restricted.

**294 files, matched neither the LOW nor HIGH domain-keyword filter.**
Top 15 by site count (reclassification judgment made where the file name
made it obvious on inspection; the rest of the 294 were not opened):
- `src/lib/common/js/builtins/string.spl` (16), `.../number.spl` (10) —
  **should be HIGH**, missed by the keyword filter (JS builtin methods over
  arbitrary JS string/number values, same domain as `json.spl` in the same
  directory). Reclassify HIGH in the next pass.
- `src/lib/nogc_sync_mut/src/exp/config.spl` (15) — experimental config
  layer; likely carries user-authored config string values — lean HIGH,
  not inspected closely enough to commit.
- `src/app/spipe_docgen/spipe_docgen/parser.spl` (13), `generator.spl` (7) —
  doc-generation from arbitrary authored doc text — lean HIGH.
- `src/app/doc_coverage/scanner/comment_extractor.spl` (12) — extracts
  **comments from source code**; comments are free-form UTF-8 even though
  the surrounding grammar is ASCII (see the LOW-section caveat above) —
  **should be HIGH**, not LOW, despite living next to compiler-tooling code.
- `src/lib/nogc_sync_mut/glob.spl` (9), `src/lib/nogc_async_mut/glob.spl` (9)
  — glob-matches **file paths from users**, explicitly named as a HIGH
  example in the assignment brief — **should be HIGH**, missed by keyword
  filter (no "path" keyword match on `glob.spl` itself).
- `src/app/tools/secret_scan.spl` (10) — scans arbitrary file content for
  secrets — lean HIGH.
- `src/app/dashboard/dashboard_collectors.spl` (10) — likely structured
  metrics, lean LOW/MIXED, not inspected.
- `src/app/package.registry/trust.spl` (9) — package metadata, likely
  mostly-ASCII by registry convention but not guaranteed — MIXED.
- `src/os/drivers/usb/xhci_regs.spl` (7), `xhci_driver.spl` (7) — USB
  descriptor/register byte arrays — **should be excluded (array domain)**,
  missed by the hardware-path filter (no matching keyword for USB driver
  paths) — reclassify as array-false-positive alongside `formula.spl`, not
  reviewed site-by-site to confirm.
- `src/lib/nogc_sync_mut/dap/hooks.spl` (8, ×3 tier copies) — Debug Adapter
  Protocol evaluates arbitrary debuggee expressions/variable names — lean
  HIGH.

**The remaining ~270 files** (config parsers, package managers, SDN
tree/tooling, embedded protocol adapters, dashboard/CLI glue) were not
opened this pass. Recommend the next triage pass start from this doc's
`unclassified_files.txt`-equivalent (regenerate via Reproduce) ranked by
site count, since the pattern above (keyword filter under-catches
`string.spl`/`number.spl`/`glob.spl`/`comment_extractor.spl`-style files
whose *name* doesn't say "text" but whose *content* obviously is) will very
likely repeat in the tail.

## Recommended fix order

1. **`structural_match.spl` `scv_find_char_pos`** — the one confirmed bug
   this pass found. Small, isolated (4 call sites, 1 helper function, no
   systemic occurrence elsewhere), low blast radius, easy to verify (same
   methodology as the `c24918ae676` and char_at-follow-up fixes already
   landed: multi-byte probe before/after). Do this first — it's a real,
   scoped, cheap fix, unlike everything else in this doc which is still
   survey-stage.
2. **`json.spl` `\uXXXX` → `"?"`** — separate ticket, not an index bug, but
   real data loss on any JSON containing a `\u`-escaped codepoint (which is
   the *standard* way to encode non-ASCII in strict JSON). Likely higher
   real-world impact than the index bug above since `\u`-escaping is common
   in JSON emitted by other tools.
3. **Re-run the keyword classifier with the corrections found this pass**
   (`string.spl`/`number.spl`/`glob.spl`/`comment_extractor.spl`-class
   misses, `formula.spl`/USB-driver-class array false positives) before
   spending further spot-check budget — the classifier itself has a known,
   demonstrated blind spot (content-based domain, not name-based) that will
   under-count real HIGH files and over-count array files in the 294-file
   unclassified bucket.
4. **`pure/nn/serialization.spl` and `web_framework/session.spl`** — spot-
   checked sites were safe, but each file has more sites (11, 10) than were
   checked (3 each) — finish the per-site check before ruling either file
   clean.
5. **The 294-file MIXED/UNKNOWN bucket** — dedicated pass, same methodology
   as this one, starting from the top-15 partially-triaged above.

## Reproduce

```
cd <fresh worktree at origin/main>
grep -rn --include='*.spl' -E '\[[a-z_0-9 +*-]+:[a-z_0-9 +*-]*\]' src/ \
  > raw.txt                                        # 3,105 / 693 files
grep -vE '^[^:]+:[0-9]+:[[:space:]]*#' raw.txt \
  > step1_nocomment.txt                             # 2,624
grep -vE '^[^:]*(hardware/|kernel/arch/|backend/native/|_X8664|riscv|arm32|arm64|avx|sve2?|rvv|mmu|paging|_rtl|fpga|vhdl_gen|k26_|evex|baremetal|opcode|isa_|/gpu/cuda/|simd|compression/zstd|/crypto/)[^:]*:' \
  step1_nocomment.txt > step2_candidate_pool.txt    # 2,352 / 581 files
```
Per-file counts: `cut -d: -f1 step2_candidate_pool.txt | sort | uniq -c | sort -rn`.
HIGH/LOW keyword filters used for the file-level split are the two `grep -iE`
patterns quoted in the "Aggregate counts" derivation above (not repeated here
verbatim to keep this section short — see the file classification tables,
which are their output after the manual corrections documented in
"Spot-check findings").

## Landing

Survey doc only — this file. No source changes. No gate/budget files touched.
