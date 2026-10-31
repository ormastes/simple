# jira_curl_search stops after one page

Status: fixed 2026-10-31, found by the emulated specs.

`jira_curl_search` (`src/app/devhub/adapter_jira_curl.spl:431`) sends one POST to
`/rest/api/3/search/jql` and never reads `nextPageToken`, although the file header
(`:14`) names that pagination. On Jira Cloud a search whose results span more than one
page returns only the first, with exit 0 and no truncation note, so `devhub jira search`
and `devhub tasks list --backend jira` silently under-report.

Data Center `POST /rest/api/2/search` has the same gap with `startAt`/`total`, not
exercised by the spec.

## Reproduction

`test/03_system/app/devhub/feature/devhub_jira_emulated_spec.spl`, scenario "follows
nextPageToken to collect every issue the limit allows". The emulator serves a first page
carrying `nextPageToken` and expects a second POST. Observed: `server saw 1 request(s),
expected 2`, and ACME-3 absent from the output. The spec failed until the fix below.

## Fix

`jira_curl_search` follows `nextPageToken` until it is absent or `--limit` is reached. It fails loudly at `JIRA_SEARCH_MAX_PAGES` (100) or on a repeated token instead of truncating. Data Center `startAt` paging is still open and unexercised.
