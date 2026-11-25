# summary_store: published summary reads back as absent (2026-11-26)

Status: verification-pending (fix landed; becomes fixed only after native verification)

## Symptom

`test/01_unit/compiler/cache/summary_store_byte_paging_spec.spl` test 1
("preserves every UTF-8 byte boundary, continuation, and page digest") fails
with `try: early return`, both on the base code (before the strict UTF-8
page-boundary fix) and after it.

## Repro

1. `SummaryStoreV1.memory()`, then
   `store.publish(summary, sha256_text("paging-ast"), "generated/untrusted;public-only")`
   for a summary at path `pkg/é한😀.spl` (snapshot `sha256_text("paging-unicode")`).
2. Wrap it in `VirtualSourceStoreAdapterV1.new(store, ...)`.
3. `facade.read(paging_auth(), snapshot, uri, 0, 1)` returns `Ok` with
   `present=false`, so the spec's `.value?` returns early.

Observed with seed `C:/dev/wt/bound3x-target/release/simple.exe`.
Tests 2 and 3 of the same spec (same publish helper, other paths) pass.

## Impact

The test's page-loop step, which checks that pages end on UTF-8 scalar
boundaries and join back to the full text, never runs, so that part of the
paging contract has no executed coverage.

## Root cause

On this seed, `text.len()` counts Unicode scalars, while `text.slice(a, b)`
takes UTF-8 byte offsets. Probe: `"ab/é한😀.spl/_tldr.spl"` has `len()` 20,
`byte_len()` 26, and `slice(3, 10)` returns `é한�` (a split emoji).

- `_uri_path_v1` (`src/compiler/80.driver/cache/summary/summary_store_v1.spl`)
  computed `uri.slice(prefix.len(), uri.len() - suffix.len())`. For a
  non-ASCII path this returns a corrupted path, so the store lookup misses
  and `stat`/`read`/`page` answer `present=false`. ASCII paths are
  unaffected, which is why byte_paging tests 2 and 3 pass.
- `rendered_size` in `stat`, `read` and `page` came from `.len()` (scalars),
  while the read/page cursors index bytes.

- Second cause, hidden behind the first: `stat`, `read`, `page` and the stored-summary decode used `match opt: case None: return ...; case value: value`. The catch-all binds the whole Option, so `path` was `Some(...)`. Interpolated into the page digest and `logical_path` it rendered as `Option::Some(pkg/...)`, so every page digest disagreed with the documented formula (byte_paging test 1 page loop, 16 mismatches) and `module_relative_utf8` carried the wrapper text.

## Fix

The slice and all three `rendered_size` values use `.byte_len()`, and the four
Option matches use `case Some(value): value`. Regression
spec: `test/01_unit/compiler/cache/summary_store_unicode_path_spec.spl`. It
fails on the base code (both non-ASCII lookup tests red, ASCII control green) and passes with the fix. byte_paging test 1
now runs its page loop.

## General trap: `len()` arithmetic in `slice()` offsets

Any `x.slice(..., ... .len() ...)` silently corrupts non-ASCII text: the
offsets are scalar counts but `slice` reads them as bytes. Use `byte_len()`
(and byte-index search results) for offsets passed to `slice`.

Similar sites on paths/URIs/URLs found by
`grep -rnE "\.slice\([^)]*\.len\(\)" src/compiler src/lib`, filtered to
slices taken on path/uri/url values. These are NOT fixed in this change; each
needs its own check of whether its index source is in bytes or scalars:

- `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl:152` `path.slice(0, path.len() - old_suffix.len())`
- `src/compiler/90.tools/fix/rules/impl_/lint_bool.spl:42` `type_path.slice(at + ".param.".len())`
- `src/lib/common/js/node/path_module.spl:54` `path.slice(last_slash + 1, path.len())`
- `src/lib/common/js/node/path_module.spl:77` `path.slice(last_dot, path.len())`
- `src/lib/common/traceability/conventions.spl:23` `path.slice(rule.source_root.value.len(), end)`
- `src/lib/editor/unified/project_navigator.spl:107` `path.slice(root.len(), path.byte_len())` (mixes `len` and `byte_len`)
- `src/lib/gc_async_mut/web/browser_session_url.spl:321` `url.slice(origin.len(), url.byte_len())` (mixes `len` and `byte_len`)

The unfiltered grep has 70 hits across `src/compiler` and `src/lib` (for
example `ui/host_env_contract.spl` x8 and `tooling/easy_fix/rules.spl` x5).
Most slice non-path text, but they share the same unit risk.
