# `url_decode` never decodes `%XX` escapes

Status: OPEN. Filed 2026-08-18.
Found incidentally during the mixed byte/codepoint indexing audit
(`mixed_byte_and_codepoint_indexing_defect_class_2026-08-18.md`) — this is a
SEPARATE defect from the indexing bug that audit fixed in the same function.

## Defect

In `url_decode` (`src/lib/nogc_async_mut/http_client/types.spl`, and its
duplicate in `src/lib/gc_async_mut/http_client/types.spl`), the `%XX` branch
parses the hex pair with `hex.parse_int(16)`, which returns `Option<i64>`, and
then calls `.to_char()` on it. On an un-unwrapped Option that call silently
no-ops rather than failing, so **`%20` never becomes a space** and no percent
escape is ever decoded. It fails silently — no error, no crash, wrong output.

## Impact

Any HTTP client path that percent-decodes a URL, query string, or form body
returns the raw `%XX` text. Two of the four stdlib trees carry the copy.

## Wanted

Fix per the Fix test standard
(`doc/03_plan/infra/binary_runtime_hardening/plan.md` § Fix test standard):
- **Reproduce**: `url_decode("a%20b")` must currently return `"a%20b"`; after
  the fix `"a b"`. Capture the pre-fix output verbatim.
- **Similar cases**: `%2F`, lowercase `%2f`, `%%`, a trailing bare `%`, `%X`
  (one hex digit then end), an invalid pair `%ZZ`, `%` runs, and a
  percent-encoded multibyte UTF-8 sequence (`%C3%A9` -> `é`) — that last one
  interacts with the indexing fix already applied here, so it must be asserted.
- Fix BOTH tree copies (they are duplicates; note the cross-tree dedup map,
  `doc/08_tracking/dedup/cross_tree_duplication_map_2026-08-18.md`).

Related smell worth a separate look: `.to_char()` silently no-opping on an
`Option` receiver is the kind of no-error-no-effect behaviour that hides bugs.
Whether that is the method's intended contract or a dispatch gap should be
checked — if unintended, it is a compiler/stdlib defect in its own right.
