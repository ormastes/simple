# Jira Data Center paginated search

Status: AUTHORED_UNRUN. This authored manual is not spipe-docgen output.
No runtime RED/GREEN, zero-stub result or measured coverage is claimed.
Proof class: production CLI plus local HTTP mock (when executed).

Spec: `test/03_system/app/devhub/feature/devhub_jira_dc_pagination_spec.spl`

Spec SHA-256: `56aaca803072eef3af992fff2f64a8680301a386c9d8e3483b0f095c878509f2`

## Operator flow

1. Start the local emulator and configure Data Center Bearer auth at a /jira context.
2. Serve two issues from startAt0 with total3 and request a user limit5.
3. Require the second POST to carry startAt2/maxResults3, and all three ordered keys.
4. Require one request for limit2 and for an empty total0 response.
5. Return a repeated offset, a stalled empty page, a string total, or missing startAt;
   require failure and exact request count, rather than a successful truncated set.
6. Stop the emulator.

REQ-DEVHUB-JIRA-DC-PAGING-001 owns steps2–4. REQ-DEVHUB-JIRA-DC-PAGING-002 owns
step5. Response framing is JSON because this is Jira's explicit HTTP wire protocol.
All values are synthetic. The local emulator checks actual requests from DevHub;
there is no test reimplementation of the paging loop.

## Fixture provenance and hashes

Primary contract: [Atlassian Data Center Search API](https://developer.atlassian.com/server/jira/platform/rest/v11002/api-group-search)
and [REST examples](https://developer.atlassian.com/server/jira/platform/jira-rest-api-examples/).
Fixtures are authored examples, not captured account responses.

- `test/fixtures/devhub/emulated/jira/search_dc_bad_total.json`: SHA-256 `33709edad51ed2cc86055b1618e7063f515cd71e051d1336886942b3b5d4097a`
- `test/fixtures/devhub/emulated/jira/search_dc_empty.json`: SHA-256 `37b5d298a25aa1889c249f29cebd5ecc8d277a835b9a867bfe8b3fdf03b0bd39`
- `test/fixtures/devhub/emulated/jira/search_dc_first.json`: SHA-256 `d647c6c0a7e25f64ffaebcc86a2ef562849e98bfa9c77d7fb44fe85954a0b1b9`
- `test/fixtures/devhub/emulated/jira/search_dc_last.json`: SHA-256 `9fa67b8fcee34e566488457ec1a2a7cc73de43185cc0c2edb1de5ed17d4a33e5`
- `test/fixtures/devhub/emulated/jira/search_dc_missing_start.json`: SHA-256 `c51c27ed6d04147ce9890e765597177b30f47e6ed978de9b20f8cbe18f35a81d`
- `test/fixtures/devhub/emulated/jira/search_dc_stalled.json`: SHA-256 `789bdae3f967b26d3c9608897a9e7a7168a0bbd2ba6580820a9e5b1964670e96`

## Pending admission

With an admitted self-hosted runtime, run this focused spec and the existing Cloud
pagination scenario, preserve actual process logs and emulator request transcript,
then run spipe-docgen with zero stubs. Until then, source review does not qualify
execution. No external Jira account is contacted by these tests.
