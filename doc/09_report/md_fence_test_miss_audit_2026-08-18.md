# Markdown fence test-miss audit (lane MDFENCE)

Date: 2026-08-18. Scope: which Markdown code-fence tests the sdoctest runner
MISSES. Follows `doc/07_guide/infra/detector/detector_standard.md` (c5a63c36c91):
every number below is labelled COUNT or UPPER BOUND, and the one classifier that
could be a detector carries a MEASURED FP rate.

Machine-readable miss list for lane TOOL:
`doc/09_report/md_fence_miss_list_2026-08-18.tsv`
(columns: `path:line` TAB `bucket` TAB `info-string` TAB `classification`).

## 1. The ACTUAL accept predicate (not the documented one)

`src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:80`

```text
if trimmed.starts_with("```simple") or trimmed.starts_with("```spl")
   or trimmed.starts_with("```sdoctest"):
```

- **Prefix, not equality.** `` ```splendid ``, `` ```simple-ish `` would be
  accepted. Latent only: **0 such fences exist today (COUNT)**.
- Close is `trimmed == "```"` (`extractor.spl:114`). A fence closed with
  `` ```` `` or with trailing text is not a close.
- A block is registered only if `final_lines.len() > 0` (`extractor.spl:119`) —
  empty fences are silently dropped, matching the documented contract.
- If a fence never closes, `in_code_block` stays true to EOF and the block is
  **never pushed** — and every later fence in that file is swallowed as its body.
  There is no diagnostic. This is the only silent-swallow path in the extractor.
- `text` is not special-cased anywhere; it is simply not one of the three
  prefixes. Contract holds.

## 2. Where the Markdown roots are declared — the class that matters

`config/sdoctest.sdn`, loaded at `src/app/test_runner_new/test_runner_main.spl:1175`
(the only live call site; `test_runner_modes.spl:147` is commented out).
Fallback defaults, used only when the file is absent:
`sdoctest/config.spl:26-40`.

Roots: `README.md`, `CLAUDE.md`, `doc/`, `examples/`, `.claude/skills/`.
Ignore globs (`config/sdoctest.sdn:21`) subtract **eight** `doc/` subtrees:
`11_archive, 09_report, 06_spec, 05_design, 01_research, 03_plan, 10_metrics,
08_tracking`. Walk + filter: `discovery.spl:48-71`, ignore match
`discovery.spl:78-83`.

Consequence: a fence outside a root, or inside an ignored subtree, is a miss the
extractor can never see, whatever its info string.

## 3. Measured buckets

Scanner: deliberately over-collecting — every ` ``` ` line, any info string,
bucketed by the first token. 18,053 Markdown files under the configured roots;
**191,182 fences (COUNT)**. Plus 2,571 Markdown files outside every root.

| bucket | count | label |
|---|---|---|
| runnable-lang (`simple`/`spl`/`sdoctest`) in a LIVE root | 1,715 | COUNT — these are seen |
| (a) bare-info-string fences in a LIVE root | 940 | COUNT of fences; see §4 for what they mean |
| (b1) runnable-lang in an IGNORED `doc/` subtree | **138,227** | COUNT of fences, UPPER BOUND as "missed tests" |
| (b2) runnable-lang in an UNCONFIGURED root | **164** | COUNT of fences, UPPER BOUND as "missed tests" |
| (c) unclosed fences | **RETRACTED — see below** | was 18/7-in-live-roots; corrected to 0 live-root defects |
| (c) empty runnable-lang fences | 3 | COUNT — **1** in a live root |
| `text` fences (live roots) | 2,076 | COUNT — correctly non-runnable |

(b1) is dominated by `doc/06_spec` at **122,577** — generated spec mirrors that
`.claude/rules/structure.md` marks DO-NOT-REFACTOR. Calling all 138,227 "missed
tests" would be dishonest: the ignore list is a deliberate policy choice, so this
is an UPPER BOUND on policy-excluded fences, not a defect count. The remaining
15,650 (09_report 11,182; 01_research 1,694; 05_design 1,603; 08_tracking 783;
03_plan 75; 10_metrics 30; 11_archive 283) are the arguable part.

(b2), 164 fences, is the genuinely surprising class: `.spipe/**` (67+),
`.codex/skills/**` (20), `.claude/agents/**` (12), `.claude/memory/**` (7),
`.claude/plan.md` (6), `src/**` (24), `test/**` (4). `.claude/skills/` is a
configured root but its siblings `agents/` and `memory/` are not.

**(c) unclosed — RETRACTED.** *Derivation of the change:* v1 of this report
counted 18 unclosed fences (7 in live roots) using a scanner that never stripped
`\r`, so its `trimmed == "```"` close test could not match a CRLF closer — but
`str_trim_left/right` in `src/lib/common/string_core.spl:110` lists `"\r"` in
`is_whitespace_char`, so the extractor that actually reads these files closes
them fine. Lane UNCLOSED reproduced the false positive with a second,
independent CommonMark-model scanner, and its guard's mutation M2 (blinding the
CR-strip) fires on all 7 non-defects — the anti-FP invariant is load-bearing and
demonstrably explains the old number.

Re-adjudicated, the 7 live-root "unclosed" fences split two ways, neither a lost
test (COUNT, verified per file):

- **4 CRLF artifacts** — `doc/07_guide/tools/README.md:53`,
  `examples/10_tooling/trace32_tools/README.md:11`,
  `.../cmm_lsp/README.md:21`,
  `examples/10_tooling/llm_cli_tools/doc/research/claudeignore_research.md:10`.
  Well-formed to the real predicate.
- **3 stray trailing fence markers at EOF** — `doc/07_guide/infra/testing/coverage.md:457`
  (bare ` ``` `), `doc/07_guide/lib/misc/markdown_document_decoration.md:222`
  and `doc/07_guide/lib/api/sdn_graph.md:154` (both ` ```` `). Each is the last
  line of its file, so the "swallowed" region is empty.

**Payoff of fixing all 7: 0 tests restored.** Five of the seven files contain no
`simple`/`spl`/`sdoctest` fence at all; in the other two (`coverage.md`, 12
runnable fences; `markdown_document_decoration.md`, 1) every runnable fence
precedes the stray marker and is already extracted.

Lane UNCLOSED's CR-tolerant re-scan of 37,147 `.md` files finds **12** genuinely
unclosed fences repo-wide (COUNT), all in ignored `doc/` subtrees, `.spipe/`,
`src/`, or `.claude/worktrees.pre_migrate_backup/` — **none reachable by
sdoctest**, and mostly doubled or trailing-text closers rather than lost tests.

The one real live-root defect in this family is an **empty** runnable fence:
`doc/02_requirements/app/testing/easy_fix.md:38`.

## 4. Bare-info-string bucket: hand-adjudicated, and it is mostly noise

Sample: **N = 32**, drawn pseudorandomly (seed 20260818) from the 940 live-root
bare fences, hand-classified by reading the first 6 body lines of each.

- genuinely runnable Simple: **1/32** (`doc/04_architecture/compiler/simd/simd_unified_architecture.md:455`, a `class` declaration)
- Simple-flavoured but not standalone-runnable fragments: 2/32
  (`.../simd_strict_emit_errata.md:264` uses Rust `[u8; 6]`; `doc/07_guide/os/fs_driver.md:372` is a bare `case` arm)
- not Simple at all: 29/32 — ASCII diagrams, x86/RISC-V asm, shell transcripts,
  YAML, tables, log output, prose prompts

> **FP-RATE: 31/32 (96.9%) on "32 pseudorandom live-root bare-info fences,
> seed 20260818", measured 2026-08-18, method: hand adjudication of the first 6
> body lines of each.**

So a detector that flags bare fences as missed tests is ~97% false positive and
must stay ADVISORY. **The bare bucket is not where the misses are.** Lane TOOL
should not build the checker around it.

## 5. Verdict

The extractor's fence predicate is essentially correct: it sees what it is
pointed at, and `text` works as the documented opt-out. The misses are entirely
**a targeting problem plus one silent-swallow bug**:

1. ~~7 unclosed fences in live roots~~ **RETRACTED**: 4 were CRLF artifacts of
   this report's own scanner and 3 are stray EOF markers; 0 tests are lost, and
   the 12 genuinely-unclosed fences repo-wide are all unreachable by sdoctest.
   The surviving live-root defect in this family is a single EMPTY runnable
   fence, `doc/02_requirements/app/testing/easy_fix.md:38` (COUNT).
2. 164 runnable-lang fences sit in Markdown no configured root reaches (UPPER BOUND).
3. 138,227 sit in ignored `doc/` subtrees — policy, not bug, but undocumented as
   a deliberate test-coverage decision (UPPER BOUND).
4. The prefix (not equality) match at `extractor.spl:80` is a latent
   over-acceptance with 0 present-day instances (COUNT).

Recommended detector shape for lane TOOL: gate on (1) and (2), which are small
and adjudicable; report (3) as an explicitly-labelled UPPER BOUND; do **not**
gate on bare-info fences at a measured 96.9% FP.

The retraction in (1) cuts the same way as §4's result and was found the same
way: an unmodelled text scan over this tree is overwhelmingly noise. Any
Markdown-fence detector MUST strip `\r` before its close test and MUST model the
real predicate at `extractor.spl:80,114` — a scanner that does neither will
manufacture exactly the defects retracted here.
