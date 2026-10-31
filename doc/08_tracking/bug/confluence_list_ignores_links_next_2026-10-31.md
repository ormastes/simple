# confluence_list_pages stops after one page

Status: open. Found 2026-10-31 by the emulated Confluence spec.

`confluence_list_pages` (`src/app/devhub/adapter_confluence.spl:246`) sends one GET and
never reads `_links.next`. `confluence_search_pages` (`:333`) has the same shape but was
not exercised. Confluence caps `limit` server-side, so asking for more than that cap
returns fewer pages, with exit 0 and no truncation note.

## Reproduction

`test/03_system/app/devhub/feature/devhub_confluence_emulated_spec.spl`, scenario "follows
_links.next to reach every page". Observed: `server saw 1 request(s), expected 2`. The
spec stays RED.

## Unblock

Follow `_links.next` until `limit` pages are collected, with a page cap. `_links.next` is
relative to `_links.base`, so resolve it against that and refuse any other origin, as
`outlook_page_error` does for Graph.
