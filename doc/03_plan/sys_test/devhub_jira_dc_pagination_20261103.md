# Jira Data Center search pagination repair

Bug: jira_search_ignores_next_page_token_2026-10-31, canonical P1 open at intake.
Base: d591d1df36f4bad9692c8eeab65c1a3a7ba69e6e. Scope: DevHub Jira curl adapter.
Test-first commit: 20104501cd5. Tests authored before repair; no admitted runtime,
so neither an observed RED nor GREEN is claimed. No bootstrap or external account
requests. Canonical bug status is not changed by this source-only repair.

## Primary contract

Atlassian Data Center search documents POST /rest/api/2/search with integer
startAt and maxResults, and response issues/startAt/total metadata:
https://developer.atlassian.com/server/jira/platform/rest/v11002/api-group-search
https://developer.atlassian.com/server/jira/platform/jira-rest-api-examples/

Cloud enhanced search uses nextPageToken on /rest/api/3/search/jql:
https://confluence.atlassian.com/jirakb/run-jql-search-query-using-jira-cloud-rest-api-1289424308.html

Official search excerpts checked 2026-11-03. Fixtures are synthetic JSON wire
responses authored from these contracts, not copied production account data.
REQ-DEVHUB-JIRA-DC-PAGING-001: request offset0 then advance by actual issue count;
honor the remaining user limit and stop at total. A server maxResults cap is not
proof it returned that many issues. Ordinary response offset2 is covered.
REQ-DEVHUB-JIRA-DC-PAGING-002: missing, negative, nonintegral/non-numeric metadata,
mismatched response offset, non-array issues and no progress with outstanding
results must fail explicitly; retain the existing 100-page ceiling.

## Owner change and regression

jira_curl_search chooses the Data Center offset protocol using the same deployment
selector as the URL. Exact nonnegative JSON integer values are decoded without
silent zero defaults; integral floats are admitted only in the exact f64 range.
Returned offset must match the request. Advance by raw returned issue count,
using an overflow guard; caller limit controls collected issues and requests.
Cloud token tracking, repeated-token refusal, HTTP errors and auth stay unchanged.

The focused local socket emulator invokes actual devhub jira search through the
production CLI/curl transport. Expected exact POST bodies assert no Cloud token
leaks into DC requests; output asserts ordered ACME-1/2/3. Cases: two capped pages,
requested limit, zero total, repeated offset, stalled empty page, string total,
missing offset; final scenario releases the emulator. Existing Cloud token
scenario is retained in devhub_jira_emulated_spec.spl.

## Verification status

AUTHORED_UNRUN for Simple regression execution, native compile, docgen and branch
coverage. Python only validates synthetic fixture structure/hashes; it does not
simulate the paging implementation or supply a runtime PASS. Existing direct-env
working/staged guards and git whitespace checks are static gates only.
Final source admission requires Astra exact-commit review; landing owner is root.
