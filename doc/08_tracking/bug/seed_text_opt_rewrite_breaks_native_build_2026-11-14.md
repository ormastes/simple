# Seed native-build rewrote `text?` to `text`, breaking Option matches (2026-11-14)

Status: partial (verification-pending for the rewrite fix; stall still open)

## Symptom
Seed `native-build` of devhub / llm_caret / mail_credentials timed out at 900 s.
A `match s: case Some(v)` over a `text?` param/local failed SPL-PAT-001
("expects Option<T>, found text").

## Root cause
`compile_file_to_object` (src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs)
unconditionally did `source.replace("text?", "text")` on the non-bootstrap path,
erasing the Option type.

## Fix
New helper `normalize_text_opt_if_unparseable`: parse the pristine source first;
rewrite only if the parse fails (same parse-first rule as the module loader).

## Evidence
Tests in native_project/tests.rs (`cargo test --profile bootstrap -p simple-compiler --lib text_opt_`):
- with fix: 2 passed, 0 failed.
- helper forced to the old unconditional rewrite: `text_opt_kept_when_source_parses` FAILED, other passed.
- fix restored: 2 passed.

## Status: partial
After the fix, with a freshly built bootstrap-profile seed, devhub, caret and
mail_credentials still exit 124 at the 600 s timeout (604 s wall each, run in
parallel) with no error line (logs end with `workarounds: incomplete coverage`,
only visibility/gc warnings). No binary was produced. Stall cause is under
separate investigation; this fix removes one real cause only.
