# caret wiki_write appends `.md` but wiki_read does not — a page cannot be read back by the id used to write it

**Date:** 2026-08-25 · **Severity:** MEDIUM (silent round-trip failure in a shipped tool) · **Status:** OPEN
**Found by:** the acceptance spec (`test/03_system/app/llm_caret/caret_agent_infra_acceptance_spec.spl`)

## Symptom
With the local markdown backend:

```
wiki_write(page_id: "a/b", …)   -> writes <root>/a/b.md
wiki_read(page_id: "a/b")       -> "page not found"
```

`wiki_write` (`src/app/llm_caret/infra_wiki.spl`) appends `.md` to an
extensionless `page_id`; `wiki_read` / `_local_read` treat `page_id` as a
literal path. So the id a caller just wrote with does not read back.

## Why the acceptance spec is still green
The spec uses the canonical `.md`-bearing id — the exact form `wiki_search`
emits — so it exercises the supported path rather than papering over this.
The asymmetry is only reachable when a caller invents an extensionless id.

## Fix direction
Make one normalisation function own the id -> path mapping and call it from
write, read, and search, so all three agree; decide explicitly whether the
canonical id carries `.md` (then `wiki_write` should return the normalised id
it actually used) or does not (then `_local_read` must append it). Ship a
reproduce example (`write("a/b")` then `read("a/b")` round-trips) plus
similar cases: id with a different extension, nested directories, an id that
already ends in `.md`, and the Confluence backend's id handling.

## Unblock condition
`wiki_read(wiki_write(id).page_id)` returns the written body byte-identically
for every id form the tool accepts, pinned by a spec.
