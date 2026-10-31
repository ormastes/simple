# confluence_list_pages stops after one page

Status: fixed 2026-10-31, found by the emulated specs.

`confluence_list_pages` (`src/app/devhub/adapter_confluence.spl:246`) sends one GET and
never reads `_links.next`. `confluence_search_pages` (`:333`) has the same shape but was
not exercised. Confluence caps `limit` server-side, so asking for more than that cap
returns fewer pages, with exit 0 and no truncation note.

## Reproduction

`test/03_system/app/devhub/feature/devhub_confluence_emulated_spec.spl`, scenario "follows
_links.next to reach every page". Observed: `server saw 1 request(s), expected 2`. The
spec failed until the fix below.

## Fix

`_confluence_collect` follows `_links.next` for list and search, with a 100-page cap and a repeat check. `confluence_next_url` only allows the configured REST content root and ignores the server-supplied `_links.base`. Scenario "rejects a next link that would send credentials to another host" pins that.
