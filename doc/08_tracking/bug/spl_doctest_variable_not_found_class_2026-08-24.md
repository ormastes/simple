# SPL doctest class `semantic: variable X not found` — triage 2026-08-24

Status: PARTIALLY FIXED (net family green); residue below is real and open.

## Verdict: NOT a harness artifact

The class was replicated **outside** the test runner using the harness's own
`extract_doctests` + `build_spl_doctest_code` (probe dumped 319 composites for
the 92 failing files, each run directly through the seed). The class reproduces
byte-for-byte, so it is not extractor damage of the `6c178bf4a30` kind.

Counts (both correct, different denominators):
- 33 — class map, *first* reason per failing block.
- 63 — this triage, *any* occurrence per composite.

## Cross-tree stdlib reads: real, but REFUTED as the cause

strace of a composite in `/mnt/data/tmp` shows resolution is cwd-first
(805 opens under the lane worktree) with a compiled-in fallback to
`/mnt/data/worktrees/seed-deploy-1`; **92 of those fallback opens succeed**
(runner-infrastructure modules: `spec/*`, `io_runtime`, `process_ops`,
`file_ops`). Real cross-tree contamination, worth its own fix, but it does not
explain this class: the missing symbols exist in *no* tree.

## Sub-class C — not a doctest defect at all (2 blocks)

`src/compiler/15.blocks/blocks/error_helpers.spl` fails **source-alone**
(`./bin/simple <file>` with no doctest appended) with
`error: semantic: variable \`i64\` not found`. Blocks L28/L80 merely inherit it.
Of the 92 failing files, 7 fail source-alone; 2 of those with this message.

## Sub-class A — missing `use` in later doc blocks (FIXED for net)

A module docstring's first fenced block carries the imports; later blocks reuse
the types without re-importing, and each block compiles independently.

Fixed in this change (`src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/net/__init__.spl`,
blocks at lines 262/296/317/344/359): added the missing `use` and wrapped each
block in a named example function, because these blocks perform live network
I/O at top level and can therefore never pass as *executed* doctests — compile-
checked is the honest contract for a usage illustration. Verified:

    ./bin/simple test --spl-doctest src/lib/nogc_sync_mut/net/__init__.spl
    SPL Doctest: 13 passed, 1 failed, 0 skipped      (was 5 of these blocks failing)

The 1 remaining failure is a different class (`unknown extern function: url_parse`).

## OPEN — documented APIs that do not exist (aspirational docs)

These blocks cannot be fixed by an import: the symbol exists nowhere in the tree.
Fixing them means implementing the API or rewriting the docs against the real one.

| symbol | doc file(s) | reality |
|---|---|---|
| `CompressionLevel`, `GzipCompressor` | `src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/compress/__init__.spl` L98/L152 | module is a docstring-only stub; none of the documented submodules or types exist |
| `SocketHandle`, `JoinSet` | `src/lib/nogc_async_mut/async_host/__init__.spl` L137/L173 | defined nowhere |
| `Promise` | `src/lib/nogc_async_mut/async/__init__.spl` L177 | exists only in `js/` and `common/testing`, not the async family |
| `pipeline.add(...)` | `http_server/{cors,csrf,access_log,rate_limit,request_validation,security_headers}.spl` | `MiddlewarePipeline` exists (`http_server/middleware.spl:50`) but has no `add` method |

## OPEN — fragment blocks (undefined locals)

`request`, `socket_fd`, `config`, `data`, `body`, `repo`, `user`, `actions`,
`api_routes`, `future`, `runtime`, `file`, `token_string`, `static_handler`,
`db_health_check`, `access_log_handler`, `query_text`, `name`, `response`.
Each starts mid-scenario. The fix is a typed example function taking the value
as a parameter — but for the `http_server` cluster that immediately surfaces the
missing-method row above, so it is blocked on the same API gap.

`src/lib/nogc_sync_mut/io/buffer.spl` L16/L25/L39 need
`use std.io.file.{FileHandle, File}`; adding it resolves `FileHandle` but the
blocks then hit `FileHandle.read_file(path)` / `.create(path)` signatures the
real `io/file.spl` does not provide — another API-vs-doc mismatch, left for the
owner rather than patched into a different-looking failure here.

---

# 2026-08-25 follow-up: the "aspirational API" map above is WRONG on three rows

A second lane re-verified every "this symbol does not exist" claim in the
section above with `grep` over `src/lib/**` plus `git log -S` over history.
**Three of the four rows are refuted.** The section above is retained
unedited for history; this section supersedes it.

Method note on the `git log -S` results: a bare `git log -S'<name>'` on this
repo returns only mass tree-wipe/restore and docs-sync commits, because it
matches the *docstring text itself*. The discriminating query is the
definition form — `git log -S'class <name>'`, `-S'struct <name>'`,
`-S'enum <name>'`, `-S'trait <name>'`, `-S'type <name>'` — which is what the
"never implemented" verdicts below rest on.

## The corrected three-way map

### (b) STALE DOC — the API exists; the doc block was wrong. FIXED.

| claim in the old map | reality | evidence |
|---|---|---|
| "`MiddlewarePipeline` exists but has **no `add` method**" — blocking 14 blocks | `add` **exists**: `me add(phase, priority, name, handler)` | `src/lib/nogc_async_mut/http_server/middleware.spl:65`; called in product code at `src/lib/nogc_async_mut/http_server/server.spl:672` inside `build_default_pipeline` |
| "`Promise` exists only in `js/` and `common/testing`, not the async family" | `Promise<T>` **exists in the async family and is exported by the very module whose docstring uses it** | `src/lib/nogc_async_mut/async/promise.spl:7`; `export Promise` at `src/lib/nogc_async_mut/async/__init__.spl:234` |
| "`FileHandle.read_file(path)` / `.create(path)` — signatures the real `io/file.spl` does not provide" | both **exist** as declared | `static fn read_file(path: text) -> Result<FileHandle, IoError>` at `src/lib/nogc_sync_mut/io/file.spl:107`; `static fn create` at `:118` |

**Root cause of the `MiddlewarePipeline` error: the previous lane read the
wrong family.** It cited `nogc_sync_mut/http_server/middleware.spl:50`. There
is no `MiddlewarePipeline` in `nogc_sync_mut` at all — the class lives only in
`nogc_async_mut`, which is also where all eight `pipeline.add(` doc blocks
live. The 14-block http_server cluster was therefore never blocked on a public
API design decision. It was Sub-class A (missing `use`) the whole time.

### (a) NEVER IMPLEMENTED — no definition form has ever existed in `src/lib` history.

`GzipCompressor`, `GzipDecompressor`, `CompressionFormat`, `SocketHandle`,
`JoinSet`. For each, the sum of `git log -S` over all five definition forms
across all of `src/lib` history is **0**. These are genuinely aspirational.
Do not implement them to satisfy a docstring.

### (c) REMOVED — none found.

No symbol in this class was implemented and later deleted.

### MIXED — `compress` is per-symbol, not per-file

The old map wrote off `compress/__init__.spl` as "a docstring-only stub; none
of the documented submodules or types exist". That is not accurate:
`src/lib/common/compress/` contains 23 real modules and its `__init__.spl`
exports a substantial API. The per-symbol truth:

| symbol | class | reality |
|---|---|---|
| `gzip_compress` / `gzip_decompress` | (b) stale signature | exist at `src/lib/common/compress/gzip.spl:21,29` as `gzip_compress(data: [u8]) -> [u8]` — **one arg, no level, no `Result`**. The doc shows `gzip_compress(data, CompressionLevel.Default)` returning a `Result`. |
| `CompressionLevel` | (b) stale shape | exists at `src/lib/common/compress/lz4.spl:8` as a **`pub struct`**. The doc uses it as an enum: `CompressionLevel.Fast` / `.Default` / `.Maximum` / `.Custom(5)`. |
| `GzipCompressor`, `GzipDecompressor`, `CompressionFormat`, top-level `compress()` | (a) never implemented | zero definition-form hits in history |

**Deliberately not rewritten here.** Fixing the compress docstrings is a real
authoring job against a half-existing API — deciding whether the docs should
describe the struct-shaped `CompressionLevel` and 1-arg `gzip_compress` that
exist, or whether the enum/Result shape is the intended target, is an API
owner's call, not a doc-hygiene edit. Mapped, recommended, left for the owner.

## Is there a `no_run` / non-executable fence marker? — answered, do not invent one

Harness: `src/lib/nogc_sync_mut/test_runner/doctest_runner.spl`.

- A block **opens** on `starts_with("```simple")` / `"```spl"` /
  `"```sdoctest"` (`doctest_runner.spl:112` and `:159`).
- The **only** thing inspected after the tag is `should_fail`
  (`:116`, `:162`). Because matching is `starts_with`, ` ```simple no_run `
  and ` ```simple,no_run ` **do** open a block and **are executed** —
  `no_run` and `ignore` are silently meaningless in this lane, not a skip.
  Writing one would create a doc block that lies about being skipped.
- The de-facto non-executable marker that **does** work: any fence tag not
  starting with `simple`/`spl`/`sdoctest` (e.g. ` ```text `) is never
  extracted. This is a real mechanism but a blunt one — it also disables
  compile-checking, so the example can rot undetected.
- The only opt-out is whole-file: `# @doctest_skip`
  (`doctest_runner.spl:570-572`), and it only affects **directory discovery**
   — an explicitly-targeted file still runs.
- `K skipped` is hardcoded to 0 for this lane (`:448, :456, :464, :548`).

**A per-block skip mechanism already exists in this repo and would not need
inventing — it is just in the other lane.** The markdown `.md` sdoctest
extractor supports ` ```simple:skip `, `:should_fail`, `:tag=` via
`parse_fence_line`/`parse_modifiers`
(`src/lib/nogc_sync_mut/test_runner/sdoctest/extractor.spl:145`), plus
`<!--sdoctest:skip-next-->` / `skip-begin/end`, with `has_modifier_skip`
at `sdoctest/types.spl:91`. **Recommendation (for the user to decide, not
done here): port `parse_modifiers` to the `--spl-doctest` lane** so a
genuinely aspirational block can be marked honestly instead of failing
forever or being hidden behind a ` ```text ` tag.

## What this lane fixed, with verbatim verdicts

The pattern is the one the net-family fix established: add the missing `use`
lines and wrap the fragment in a named example function, so the block is
compile-checked rather than executed at top level.

| file | before | after |
|---|---|---|
| `nogc_async_mut/http_server/cors.spl` | `0 passed, 1 failed, 0 skipped` | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/csrf.spl` | — | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/access_log.spl` | — | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/rate_limit.spl` | — | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/request_validation.spl` | — | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/security_headers.spl` | `1 passed, 1 failed, 0 skipped` | `2 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/http_server/middleware.spl` | — | `1 passed, 0 failed, 0 skipped` |
| `nogc_async_mut/async/__init__.spl` (Promise block) | `3 passed, 5 failed, 0 skipped` | `4 passed, 4 failed, 0 skipped` |

The `async/__init__.spl` row is a measured before/after on the same file: net
**+1 passed, -1 failed**, i.e. the Promise block specifically now passes. The
4 remaining failures in that file are other blocks (the `SocketHandle` /
`JoinSet` category-(a) ones among them) and are untouched by this change.

## Verification caveat — read this before trusting the numbers

**These were verified under the `8a47377b696` harness, not at origin/main,
because at origin/main no doctest verdict can be obtained at all**: every
`--spl-doctest` run at `6cd4f9a3381` aborts with
`error[E1002]: function `unsafe` not found` and prints no `SPL Doctest:` line.
Filed separately as
`doc/08_tracking/bug/spl_doctest_harness_aborts_unsafe_not_found_2026-08-25.md`.

`git diff --stat 8a47377b696 6cd4f9a3381` over the touched directories shows
only `http_server/static_file.spl` and `io/metal_ptr.spl` differing — neither
is a file this work edits — so the transferred verification is clean.

## Still OPEN after this lane

- **`io/buffer.spl` (3 blocks).** Refuted as an API mismatch — `FileHandle`
  has the methods. But these blocks perform real filesystem I/O on
  `/tmp/io_test_*.txt` fixtures that do not exist, so they are *executed*
  doctests that cannot pass regardless of imports. An import-only edit was
  attempted, did not produce a pass, and was **reverted rather than left in
  place changing the error's shape**. Needs either a real fixture or the
  ported per-block skip modifier above.
- **`compress` family.** Mapped per-symbol above; doc rewrite is an owner call.
- **`SocketHandle` / `JoinSet` / `Promise` blocks in the async families.**
  `Promise` is (b) and a fix is drafted; `SocketHandle` and `JoinSet` are (a).
- **`error_helpers.spl` (2 blocks).** Unchanged: not a doctest defect, the
  source fails alone.
