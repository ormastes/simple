# Windows path duality: native file APIs, raw rt_ externs, and the POSIX shell see three different files for /tmp paths

- **Filed:** 2026-09-18
- **Status:** OPEN — architectural debt; per-spec workarounds only until the
  boundary is made total.

## The three namespaces (measured on a Git-Bash Windows host)

1. `host_path_native("/tmp/x")` -> `<drive>:\tmp\x` (used by the file_ops
   wrappers that route through the boundary).
2. Raw `rt_file_*` externs called WITHOUT the boundary (e.g. the historical
   `rt_file_publish_noreplace(staged, destination)` in `file_publish_noreplace_raw`)
   receive the canonical `/tmp/x` verbatim; the Windows API resolves that
   against the current drive root.
3. `shell()` commands (Git Bash) resolve `/tmp` to the MSYS-internal temp,
   which on the measured host is NEITHER `<drive>:\tmp` NOR `%TEMP%`.

A spec that writes through one namespace and reads through another therefore
sees two different files. The `duplicate_check/cache_spec` invalidation test
pinned this: the cache hashes natively (boundary) while its fixture tokenizer
read via `shell cat` — tokens never changed, and the test failed on Windows
only. Fixed 2026-09-18 by making the spec read natively
(`file_read_text`), which is self-consistent on every platform.

## Attempted and reverted

Mapping `/tmp` -> `%TEMP%` inside `host_path_native_for` was tried and
reverted the same day: several raw rt_ call sites bypass the boundary
entirely (write and hash land in different namespaces anyway), so a partial
mapping made write-vs-hash WORSE (hashes started returning "" for files the
raw writes placed in `<drive>:\tmp`).

**Correction 2026-09-19:** the mount table on the Git-Bash host maps `/tmp`
to `%TEMP%` (`usertemp` mount) — the shell and %TEMP% agree. The real split
is exactly TWO namespaces: the native boundary (`<drive>:\tmp` for unmapped
POSIX paths) vs everything routed/MSYS-aware (%TEMP%). The reverted mapping
would have aligned the boundary with %TEMP%; it stays reverted only because
raw bypasses (since fixed for publish; `rt_file_write_text` in io_runtime
line 230 was verified to map) must be audited first.

## What would fix it properly

- Route EVERY path-taking rt_file call through `host_path_native`
  (`host_path_boundary_spec` now pins this; `file_publish_noreplace_raw` was
  the last known bypass, fixed 2026-09-18).
- Decide and document ONE /tmp convention for the Windows lane (either the
  native boundary maps /tmp -> %TEMP% AND all raw call sites are eliminated,
  or specs use a repo-local fixture dir and never /tmp).
- Until then, specs must read and write through the SAME layer (native
  file_ops or shell, not both).

## Related triage notes (2026-09-19, whole-suite run)

- ui.chromium text_metrics family (13/14 fail, "expected 0 to be greater
  than 0"): FontRenderer.browser_serif_default() finds no loadable font.
  The seed DOES export spl_fonts_call_init_blob/init_path/layout_text, so
  the SFFI backend exists; the failure is candidate-path resolution. The
  spec imports browser_serif_font_candidates from common.text_layout
  (a THIRD provider copy beside the nogc_sync_mut and gc_async_mut ones) —
  check that copy's candidates include the bundled
  assets/fonts/google-fonts paths and Windows C:/Windows/Faces before
  touching the loader. Serif candidates also lack the
  browser_platform_sans_faces()-style Windows hook that sans has.
