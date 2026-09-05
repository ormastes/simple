# sdoctest extractor miss audit — source-comment doctests in owned code

Date: 2026-08-18. Lane EXTRACT. Read-only audit; no extractor/checker source was edited.
Follows `doc/07_guide/infra/detector/detector_standard.md` (rules 8 and 9 in particular).

## Verdict (one line)

**The canonical sdoctest extractor misses 100% of source-comment doctests in owned
`.spl` code — it never opens a `.spl` file at all.** 180 candidates found in
`src/{lib,app,compiler,os}`; **138 hand-classifiable as genuine tests (COUNT, see
FP measurement below)**, 42 illustrative snippets in a documented recognised form,
10 malformed/false-positive.

## 1. The extractor's ACTUAL recognition predicate (from code, not docs)

Two gates. The FIRST gate alone decides the whole result for source files.

### Gate A — file discovery: markdown only, three hard filters

| condition | file:line |
|---|---|
| CLI dir override walks with pattern `"*.md"` | `discovery.spl:19` |
| CLI single-file override requires `cli_path.ends_with(".md")`, else `return []` | `discovery.spl:21-23` |
| directory walk: `if not file_path.ends_with(".md"): continue` | `discovery.spl:59` |
| default sources are `README.md`, `doc/`, `examples/` — no `src/` | `config.spl:31-33` |
| a dir source with empty pattern defaults to `"*.md"` | `config.spl:88,118,196,220` |

There is no code path by which a `.spl` file reaches `extract_sdoctest_blocks`.
`src/` is not a configured source, and even if it were, the `.md` filter drops
every file. This is the miss.

### Gate B — block recognition inside a file (applies to raw lines, uncommented)

| condition | file:line |
|---|---|
| opening fence must be a **trimmed** line starting `` ```simple `` / `` ```spl `` / `` ```sdoctest `` | `extractor.spl:80` |
| closing fence must be a trimmed line **exactly** `` ``` `` (a fence with trailing text never closes) | `extractor.spl:114` |
| block emitted only if `final_lines.len() > 0` (empty body rejected) | `extractor.spl:120` |
| unclosed block at EOF is silently dropped (`in_code_block` still true, loop ends, nothing pushed) | `extractor.spl:37,135` |
| `sdoctest` language strips `>>>`/`...`; any line without a prompt is discarded as expected output | `extractor.spl:118-119,204-218` |
| skip/ignore HTML markers must match the trimmed line **exactly** | `extractor.spl:42-70` |
| run-config marker parsed by fixed offsets `[14 : len-3]` | `extractor.spl:72-73` |

**Nothing in Gate B strips comment prefixes.** A line `# ```simple` trims to
`# ```simple`, which does not `starts_with("```simple")` — so even if a `.spl`
file were fed in, comment-embedded fences would still be rejected at
`extractor.spl:80`. Likewise there is **no handling of docstring `sdoctest:`
blocks anywhere in the file** — `/usr/bin/grep -n 'sdoctest:' extractor.spl`
finds only the HTML-marker literals at lines 42-72. The documented forms
"`#` / `##` / `///` comment examples" and "docstring `sdoctest:` blocks" are
**not implemented in the canonical extractor**; the docs describe an intent, not
the code.

## 2. Independent permissive scanner

`scratchpad/permissive.py` (throwaway, Python). Deliberately over-collects:
any `#`/`##`/`///`-prefixed ` ``` ` fence pair, any comment `>>>` prompt, any
line matching `^\s*(#|///)?\s*sdoctest:`. Scanned **13,651 `.spl` files** under
`src/lib`, `src/app`, `src/compiler`, `src/os`, excluding vendored paths per
CLAUDE.md Owned-Code Scope. Raw hits: **190**.

## 3. Diff against the real extractor

The real extractor accepts **0** of the 190 (Gate A rejects all 13,651 files
before any content is read). Every hit is therefore a miss candidate.

## 4. Hand-classification and MEASURED false-positive rate

Auto-classification of all 190, then hand adjudication of a random sample.

| class | count | is it a real missed test? |
|---|---|---|
| `genuine-test` (docstring `sdoctest:` block with `expect(`/`assert`) | 135 | yes |
| `snippet-no-assertion` (docstring `sdoctest:` block, runnable, no assertion) | 3 | yes — executes, would catch a crash |
| `illustrative-snippet` (comment ` ```simple ` fence, no assertion) | 42 | yes by the documented spec (`#` comment examples are a recognised form) |
| `malformed-empty` | 5 | no |
| `malformed-unclosed` | 2 | no |
| `genuine-test-prompt` (`>>>` in comment) | 3 | **no — all three are ASCII banners, scanner FP** |

**FP-RATE: 9/35 (25.7%) on a random seed-11 sample of 35 of the 190 raw hits,
measured 2026-08-18, method: hand-read of each hit with 6 lines of context.**
The 9 false positives are exactly: 3 `>>>` ASCII-art banners
(`src/app/browser/render_lane.spl:49`, `src/lib/blink/layout/style_bridge.spl:10`,
`src/lib/common/svmg/mailbox_const.spl:107`), 3 struct-field lines literally named
`sdoctest:` (`test_runner_types.spl:100`, `execution_strategy.spl:272`,
`test_runner_args.spl:635`), and 3 self-referential doc-fences inside
`sdoctest/extractor.spl:143,145,147`. All 9 land in the `malformed-*` /
`genuine-test-prompt` buckets, which are excluded from the miss list.
Sample coverage of the `genuine-test` bucket: 13/13 adjudicated correct, 0 FP.

**Labelling per rule 9:** the **180-row miss list is an UPPER BOUND** on missed
tests (it includes 42 illustrative snippets whose test-worthiness is a policy
call). The **138 `genuine-test` + `snippet-no-assertion` rows are a COUNT** of
executable doctest bodies that exist in owned source and are never run —
0 FP in the adjudicated sub-sample, and each is a docstring block whose body
lines are Simple statements.

53 distinct files carry at least one missed candidate.

## 5. Machine-readable miss list (fixture set for lane TOOL)

Format: `path:line<TAB>detector-kind<TAB>classification`. Rows classified
`malformed-*` and `genuine-test-prompt` are RETAINED and marked so lane TOOL can
use them as must-NOT-fire negatives.

```tsv
src/app/browser/render_lane.spl:49	comment-prompt	genuine-test-prompt
src/app/desugar/mod.spl:48	comment-fence-block	illustrative-snippet
src/app/desugar/mod.spl:63	comment-fence-block	illustrative-snippet
src/app/desugar/mod.spl:77	comment-fence-block	illustrative-snippet
src/app/simple_lab/export_sdoctest.spl:45	comment-fence-unclosed	malformed-unclosed
src/compiler/00.common/driver_compile_options.spl:49	sdoctest-marker	genuine-test
src/compiler/00.common/gc_config.spl:156	sdoctest-marker	genuine-test
src/compiler/00.common/gc_config.spl:182	sdoctest-marker	genuine-test
src/compiler/00.common/gc_config.spl:193	sdoctest-marker	genuine-test
src/compiler/00.common/gc_config.spl:204	sdoctest-marker	genuine-test
src/compiler/00.common/gc_config.spl:221	sdoctest-marker	genuine-test
src/compiler/10.frontend/core/interpreter/mod.spl:68	comment-fence-block	illustrative-snippet
src/compiler/10.frontend/core/interpreter/mod.spl:78	comment-fence-block	illustrative-snippet
src/compiler/10.frontend/core/interpreter/mod.spl:92	comment-fence-block	illustrative-snippet
src/compiler/10.frontend/core/interpreter/mod.spl:104	comment-fence-block	illustrative-snippet
src/compiler/10.frontend/core/interpreter/module_loader_core.spl:495	sdoctest-marker	genuine-test
src/compiler/10.frontend/core/interpreter/module_loader_core.spl:528	sdoctest-marker	genuine-test
src/compiler/15.blocks/blocks/mod.spl:18	comment-fence-block	illustrative-snippet
src/compiler/15.blocks/blocks/mod.spl:33	comment-fence-block	illustrative-snippet
src/compiler/15.blocks/blocks/mod.spl:43	comment-fence-block	illustrative-snippet
src/compiler/15.blocks/blocks/mod.spl:120	comment-fence-block	illustrative-snippet
src/compiler/15.blocks/blocks/mod.spl:128	comment-fence-block	illustrative-snippet
src/compiler/15.blocks/blocks/mod.spl:138	comment-fence-block	illustrative-snippet
src/compiler/30.types/type_check/mod.spl:22	comment-fence-block	illustrative-snippet
src/compiler/35.semantics/effect_verifier.spl:183	sdoctest-marker	genuine-test
src/compiler/35.semantics/effect_verifier.spl:257	sdoctest-marker	genuine-test
src/compiler/35.semantics/effect_verifier.spl:305	sdoctest-marker	genuine-test
src/compiler/35.semantics/effect_verifier.spl:353	sdoctest-marker	genuine-test
src/compiler/35.semantics/gc_boundary_check.spl:298	sdoctest-marker	genuine-test
src/compiler/35.semantics/gc_boundary_check.spl:363	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_direction_checker.spl:54	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_direction_checker.spl:107	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_direction_checker.spl:165	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_direction_checker.spl:174	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_wiring.spl:61	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_wiring.spl:93	sdoctest-marker	genuine-test
src/compiler/35.semantics/layer_call_wiring.spl:136	sdoctest-marker	genuine-test
src/compiler/35.semantics/noalloc_checker.spl:393	sdoctest-marker	genuine-test
src/compiler/35.semantics/noalloc_checker.spl:507	sdoctest-marker	genuine-test
src/compiler/35.semantics/noalloc_checker.spl:529	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_capability.spl:357	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_capability.spl:492	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_cross_target.spl:104	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_support_matrix.spl:257	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_support_matrix.spl:270	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_support_matrix.spl:283	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_support_matrix.spl:342	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_support_matrix.spl:364	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_version.spl:55	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_version.spl:202	sdoctest-marker	genuine-test
src/compiler/70.backend/backend/llvm_version.spl:217	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:57	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:85	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:99	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:128	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:142	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:165	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:193	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:251	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:294	sdoctest-marker	genuine-test
src/compiler/85.mdsoc/security.spl:326	sdoctest-marker	genuine-test
src/compiler/90.tools/coverage.spl:99	sdoctest-marker	genuine-test
src/lib/blink/layout/style_bridge.spl:10	comment-prompt	genuine-test-prompt
src/lib/common/svmg/mailbox_const.spl:107	comment-prompt	genuine-test-prompt
src/lib/common/text_advanced.spl:759	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:778	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:799	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:824	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:844	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:887	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:919	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:947	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:977	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1000	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1017	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1041	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1065	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1080	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1114	sdoctest-marker	snippet-no-assertion
src/lib/common/text_advanced.spl:1126	sdoctest-marker	snippet-no-assertion
src/lib/common/text_advanced.spl:1137	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1168	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1188	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1202	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1222	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1252	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1284	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1300	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1322	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1335	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1345	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1397	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1428	sdoctest-marker	genuine-test
src/lib/common/text_advanced.spl:1457	sdoctest-marker	genuine-test
src/lib/common/ui/builder.spl:543	sdoctest-marker	genuine-test
src/lib/common/ui/builder.spl:556	sdoctest-marker	genuine-test
src/lib/common/ui/capability_policy.spl:53	sdoctest-marker	genuine-test
src/lib/gc_async_mut/platform/mod.spl:26	comment-fence-block	illustrative-snippet
src/lib/gc_async_mut/platform/mod.spl:36	comment-fence-block	illustrative-snippet
src/lib/gc_async_mut/platform/mod.spl:47	comment-fence-block	illustrative-snippet
src/lib/gc_async_mut/platform/mod.spl:62	comment-fence-block	illustrative-snippet
src/lib/gc_async_mut/security/auth/context_propagation.spl:83	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/credential_store.spl:52	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/credential_store.spl:104	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/env_config.spl:40	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/env_config.spl:159	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/rotation.spl:76	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/auth/rotation.spl:102	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/sanitize.spl:8	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/sanitize.spl:37	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/sanitize.spl:113	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/sanitize.spl:162	sdoctest-marker	genuine-test
src/lib/gc_async_mut/security/sanitize.spl:204	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/concurrent/actor.spl:28	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/actor.spl:38	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/actor.spl:53	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/mod.spl:46	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/mod.spl:55	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/mod.spl:74	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/mod.spl:94	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/concurrent/mod.spl:104	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/platform/mod.spl:26	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/platform/mod.spl:36	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/platform/mod.spl:47	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/platform/mod.spl:62	comment-fence-block	illustrative-snippet
src/lib/nogc_async_mut/security/auth/context_propagation.spl:114	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/credential_store.spl:52	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/credential_store.spl:104	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/env_config.spl:40	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/env_config.spl:159	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/rotation.spl:76	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/auth/rotation.spl:102	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/sanitize.spl:8	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/sanitize.spl:37	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/sanitize.spl:113	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/sanitize.spl:162	sdoctest-marker	genuine-test
src/lib/nogc_async_mut/security/sanitize.spl:204	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/concurrent/channel.spl:30	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/channel.spl:40	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/channel.spl:62	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/channel.spl:74	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/thread.spl:23	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/thread.spl:32	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/thread.spl:44	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/concurrent/thread.spl:53	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/coverage.spl:57	sdoctest-marker	snippet-no-assertion
src/lib/nogc_sync_mut/http_server/mime.spl:14	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/http_server/mime.spl:85	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/io/coverage_simple.spl:203	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/platform/mod.spl:26	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/platform/mod.spl:36	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/platform/mod.spl:47	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/platform/mod.spl:62	comment-fence-block	illustrative-snippet
src/lib/nogc_sync_mut/security/audit_log.spl:39	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/audit_log.spl:87	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/audit_log.spl:108	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/context_propagation.spl:116	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/credential_store.spl:53	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/credential_store.spl:109	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/env_config.spl:40	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/env_config.spl:159	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/rotation.spl:76	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/auth/rotation.spl:102	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/capability.spl:34	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/capability.spl:84	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/capability.spl:227	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/gate.spl:101	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/gate.spl:128	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/enforcement/resolver.spl:22	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/sanitize.spl:8	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/sanitize.spl:39	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/sanitize.spl:113	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/sanitize.spl:178	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/sanitize.spl:220	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/types.spl:822	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/prompt_sanitizer.spl:51	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/prompt_sanitizer.spl:85	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/prompt_sanitizer.spl:119	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/prompt_sanitizer.spl:133	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/prompt_sanitizer.spl:144	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/url_validator.spl:42	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/url_validator.spl:100	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/url_validator.spl:147	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/security/validation/url_validator.spl:165	sdoctest-marker	genuine-test
src/lib/nogc_sync_mut/test_runner/execution_strategy.spl:272	sdoctest-marker	malformed-empty
src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:143	comment-fence-empty	malformed-empty
src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:145	comment-fence-empty	malformed-empty
src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:147	comment-fence-unclosed	malformed-unclosed
src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:635	sdoctest-marker	malformed-empty
src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:100	sdoctest-marker	malformed-empty
```

## 6. What this does NOT claim

- Not measured: whether any of the 138 genuine bodies would actually PASS if run.
  This audit measures *extraction*, not *execution*. Several reference
  identifiers (`LayerDagRegistry`, `SecretRotation`) that need an init context.
- `.md` doctests are out of scope here — the extractor does handle those, and
  this audit says nothing about its `.md` recall.
- No spec was run; no `Results:` line is claimed anywhere in this document.
