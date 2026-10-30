# Comment triple quotes hide later module-surface declarations

Date: 2026-10-25. Class: compiler frontend / worker surface. Status: source fix prepared; cycle-9 runtime qualification is pending.

## Evidence

A focused retained log at `build/native_probe/release100-cycle8/lexer-surface-diagnostic-6fab9956b22efcb9a39db99b664b458d19dd0276ee18a6be0d358b174977409e/compile.log` (lines 143026–143032) for source snapshot `scv-revision-v1-ef194ecbe3260c741a6862ce3cc4dc1c27d85d702754cc06a38b0a8456083936` has unresolved-name diagnostics for `pop_indent`, `char_at_pos`, `next_token`, `char_slice`, `enable_forced_indentation`, and `disable_forced_indentation`. A separate earlier provisional Phase 3 log at `build/native_probe/release100-cycle8/provisional-phase3/6fab9956b22efcb9a39db99b664b458d19dd0276ee18a6be0d358b174977409e/compile.log` records 11 unresolved lexer-surface imports, including `next_token`, two `token_text` imports, `token_start`, and `token_end`. These are separate observations and do not imply that every failure in either log has this cause.

The snapshot source declares the affected lexer wrappers after the large `CoreLexer` implementation, around lines 1790–1834; `core_lexer_token_start` and `core_lexer_token_end` are explicitly exported.

The worker surface path parses `module_surface_skeleton_v1(source)`, not the full module source. The old `_skel_string_continuations_v1` counted every `"""` sequence without lexical context. A full-line comment near `lexer_struct.spl:816` contains one such delimiter; a comment near line 1130 contains two. The odd count in the first comment switched the scanner into string mode, and the second comment did not switch it back. Later top-level wrappers were then consumed as continuation text by an enclosing body-skeleton loop. These logs are diagnostics from provisional builds; they do not establish a standalone runtime failure count.

## Fix

The scanner now recognizes comments, ordinary quoted strings and escapes, escaped-newline continuation, nested strings in ordinary interpolation, matching `'''` / `"""` delimiters, and raw-string prefix behavior. It retains one continuation flag per original line. The full source and generated skeleton are compared for canonical surface digest, including the late lexer wrappers.

Because old persisted surfaces may contain the truncated skeleton, the TLDR companion header advances from v6 to v7 and the worker sidecar header from v1 to v2. Readers reject old versions and rebuild the surface.

## Regression coverage

The skeleton spec covers comment delimiters, ordinary escaped strings, escaped-newline interpolation, raw strings, nested interpolation containing triple-quote text, matching single/double/raw multiline strings with fake column-zero declarations, and the real late lexer wrappers. Cache specs check v6 companion rejection and v1 worker-sidecar rejection/rebuild.

## Verification status

No build or test has been run for this change. Source review is pending; no runtime PASS is claimed.
