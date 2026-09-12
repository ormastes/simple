# rt-dual-implementation ratchet RED after PR #649 (2026-09-12)

## Summary

`sh scripts/check/check-rt-dual-implementation-ratchet.shs` went RED on
`origin/main` after PR #649 (`gh pr view 649`, owner: ormastes, session
`https://claude.ai/code/session_01FVXExJncXzKHBqbWfBAKok`) merged. Two
independent, unrelated causes:

## 1. Four new single-lane symbols (real debt, baselined as reviewed)

PR #649 backed four externs in `src/lib/nogc_sync_mut/sffi/fs.spl` —
`rt_fs_read_text`, `rt_file_mode`, `rt_file_atomic_write_mode`,
`rt_file_list_dir` — that had **no implementation on either side** (silent
nil on POSIX; hard link failure on MSVC, which is what surfaced the bug at
Stage 2). The PR added real C implementations
(`src/runtime/runtime_native.c:12395-12442`) to unblock the Windows link,
plus a C-lane selfcheck (`src/runtime/test/rt_bootstrap_c_lane_fs_env_selfcheck.c`).
It added **no Rust runtime implementation**.

Per the standing rt_* dual-implementation directive
(`.claude/rules/vcs.md` § rt_* dual-implementation), this is genuine new
single-lane debt: these four symbols are ordinary cross-platform file
primitives with an obvious architectural counterpart (unlike the `rt_vulkan_*`
family, which is baselined because it has no Rust-side conceptual twin at
all — GPU backend calls are inherently one-lane). Filed rather than silently
baselined:

- **Owner:** ormastes (PR #649 author)
- **Missing twin:** a Rust `fn rt_fs_read_text` / `rt_file_mode` /
  `rt_file_atomic_write_mode` / `rt_file_list_dir` in
  `src/compiler_rust/runtime/src/**`, bound by the usual alias so both lanes
  are exercised by the intensive dual-run tests the directive calls for.
- **Not verified in this pass:** whether the interpreter/seed extern
  registry path (the one `check-unbacked-extern-ratchet.shs` / the
  `interpreter-extern-registry-gap` gate cover) still resolves these four
  through the Rust runtime and would therefore still hit the silent-nil bug
  on that path even though the native/MSVC link is now fixed. `PR #649`'s
  own description scopes its verification to `cl.exe` compile + `llvm-nm`
  + a WSL POSIX syntax check + the new C selfcheck — none of those exercise
  the interpreter path. Needs a follow-up check before this is considered
  fully closed, only the link-breaking half is.
- Also unverified: whether the Rust runtime already has same-shape file
  primitives under different names that these four could alias onto instead
  of requiring a fresh port. Not found in this pass
  (`grep -rn 'rt_file_\|rt_fs_read' src/compiler_rust/runtime/src` returned
  nothing for these four names) but the broader "same behavior, different
  name" question was not exhaustively checked.

**Action taken:** baselined as `c-only` in
`scripts/check/rt_dual_implementation_baseline.txt` with a
`# TEMP-ratchet-debt PR649 (2026-09-12, reviewed)` comment block naming this
doc, rather than left red — the block is a full-line `#` comment (the guard
strips `^#` lines before parsing, confirmed by reading
`check-rt-dual-implementation-ratchet.shs:392`), so it is documentation only
and does not weaken the machine check itself. This is a debt marker, not a
closure — the missing Rust twin is still open.

## 2. `rt_transient_raw_words` false "stale" — extractor defect, NOT a real change

The ratchet also reported `rt_transient_raw_words` (baselined `rust-only`)
as STALE (no longer single-lane). Investigated and **rejected as a baseline
edit** — the symbol is not actually dual-lane in production:

- The only text matching the C-lane extractor's `rt_NAME(...) {` pattern is
  `src/runtime/test/rt_bootstrap_c_lane_fs_env_selfcheck.c:124`, a test
  **stub** added by PR #649 (`int64_t rt_transient_raw_words(...) { ... }`
  in a selfcheck harness, not a real runtime definition). Confirmed via:
  `find src/runtime -name '*.c' -not -path '*/vendor/*' -print0 | xargs -0
  grep -lE '\brt_transient_raw_words[[:space:]]*\([^;]*\)[[:space:]]*\{'`
  returns only that one test file.
- The real C implementation lives in `src/runtime/runtime_memory.c:165`, but
  its signature is written across multiple lines, so the extractor's
  single-line `grep -o` never matched it even before PR #649 — this symbol
  was already only detected via the Rust side's `extern "C" { fn
  rt_transient_raw_words(...); }` declaration
  (`src/compiler_rust/runtime/src/value/collections.rs:1890`), which the
  Rust-lane regex (`fn[[:space:]]+rt_[A-Za-z0-9_]+`) matches even though it
  is an FFI import, not a Rust definition. So the baseline classification
  `rust-only` was **always** a false read for this symbol (it should be
  dual-lane: real C def in `runtime_memory.c`, real Rust caller/binding in
  `collections.rs`), and PR #649's test stub happened to be the first thing
  that tipped the (already-wrong) rust-only classification into a
  differently-wrong "now dual, therefore stale" read.
- **Did not drop the baseline line** and did not fix the extractor in this
  pass. A narrow attempt to exclude `src/runtime/test/` from the C-lane scan
  was tried and reverted: it also flips 2 unrelated, pre-existing symbols —
  `rt_browser_http_job_free` / `rt_browser_http_job_poll`, whose only C-lane
  match is likewise `src/runtime/test/rt_browser_http_job_provider_selfcheck.c`
  — from (incorrectly) dual-lane to (correctly) single-lane-new, expanding
  the delta from 1 stale to 6 new + 18 stale total. That is a real,
  separate extractor-accuracy defect (multi-line C signatures are missed;
  test-only stubs are miscounted as implementations) affecting more than
  this one symbol, and fixing it properly needs its own reviewed change with
  its own baseline reconciliation pass — out of scope for a same-day PR #649
  reconciliation.

**Net result: the ratchet is left RED on this one entry.** `git push` for
this reconciliation must use whatever is required to get the real 4-symbol
debt landed without silently misclassifying `rt_transient_raw_words`; if
this repo's push gate treats `rt-dual-implementation` as hard-blocking with
no override, that is the correct behavior here — the fix belongs in the
extractor, not the baseline.

## Follow-up

- Fix `extract_lanes()` in `check-rt-dual-implementation-ratchet.shs` to (a)
  match multi-line C function signatures, or use `nm`-based extraction
  against a real build the way the authoritative census script does, and
  (b) exclude `src/runtime/test/` from the C-lane scan the same way
  `vendor/` is excluded. Re-run a full baseline reconciliation after, since
  the fix is known to affect at least 3 symbols
  (`rt_transient_raw_words`, `rt_browser_http_job_free`,
  `rt_browser_http_job_poll`) and likely more that haven't surfaced yet.
- Port `rt_fs_read_text` / `rt_file_mode` / `rt_file_atomic_write_mode` /
  `rt_file_list_dir` to the Rust runtime lane, or get an explicit
  architectural-exception ruling (like `rt_vulkan_*`) if they are judged to
  have no Rust-side counterpart — TBD by owner.
