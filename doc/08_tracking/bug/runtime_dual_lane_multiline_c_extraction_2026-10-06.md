# Multiline C definitions omitted by the dual-lane ratchet

The paired provider-session candidate was rejected because the C extractor
matched each physical line separately. A legitimate multiline definition such
as `rt_provider_session_call_end` was omitted even though its Rust counterpart
was counted. Exempting the symbol or changing the baseline would conceal the
scanner defect.

The C extractor now lexes each owned C file, discards comments and literals,
and recognizes an `rt_` declaration's balanced parameter list followed by a
body brace. A nonempty declaration prefix distinguishes calls; a semicolon
does not establish a definition. Post-parameter compiler attributes are
handled. Reads stop at 16 MiB plus one byte and token storage at one million
tokens per file; errors propagate to an ERROR verdict before comparison.

This is a lexical source census, not a C preprocessor or compiler. Directive
lines (including continuations) are skipped without interpreting conditions.
All conditional bodies remain visible. No global brace-depth heuristic is
used: alternative `#if`/`#else` body openings may not balance in raw source.
Macro-generated definitions still require the separate artifact census for
authoritative measurement. No test-macro exemptions were introduced.

C and Rust sets remain separate. Both revisions still use committed source
materialization, and no baseline entries changed. The paired lane separately
renames its test-only helper to avoid a misleading public-runtime prefix.

Validation, first cycle: ten actual extractor/ratchet selftest fixtures passed,
including multiline parameters and next-line braces, compiler attributes,
prototype/call/comment/string negatives, alternative conditional openings plus
a subsequent export, malformed lexical input, lane separation, and committed
content checks. One real committed comparison of
`d98e7122ad6deac136ab07fd6a68d11478a86bc2` against itself passed with 2647
single-lane symbols and zero new symbols. The frozen-baseline drift (216 new,
68 stale) was informational in delta mode and was not excused or regenerated.
Log: `build/review/dual-lexer/committed-scan.log` in the isolated worktree.

The selftest-only summary's old hardcoded count was replaced with its measured
fixture count. No compiler, Hello, or runtime build was performed. Broader paired compiler and application qualification remains pending.

Focused compatibility correction: all 59 existing Unicode verdict/comment lines were compared with the base and preserved byte-for-byte (apart from the intentional measured selftest count). The existing cache key already hashes the complete extractor script as well as both source tree IDs, so old line-scanner entries cannot be reused.

Actual paired successor scan: de40d928a00ab9011fe80001acd09a44346424fa against d98e7122ad6deac136ab07fd6a68d11478a86bc2 passed with 2647 single-lane symbols and zero new. Cache reuse was disabled for this one scan. The nine genuine C/Rust session exports are paired; the renamed test helper does not claim a runtime prefix. Retained log: build/review/dual-lexer/paired-scan.log. No compiler execution.
