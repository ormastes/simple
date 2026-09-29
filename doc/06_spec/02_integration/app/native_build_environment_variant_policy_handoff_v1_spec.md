# Native-build environment variant policy handoff V1

This component check verifies the production seam:

1. The parent collects policy once and appends one internal payload.
2. Parse-shard, HIR-shard, and real-worker launches receive the same payload;
   both worker entrypoints validate and remove it.
3. The parent does not rewrite frontend policy environment variables.
4. The full worker creates its driver with the decoded typed collection, and
   the slim parse shard projects the same collection before source loading.
5. Parse shards do not inherit selected callable session authority; their
   owner, session, and generation fields remain zero.
6. Legacy argv parsing still accepts the preserved public policy flags without
   rebuilding policy from process environment variables.
7. The warm receipt key includes the policy-and-target cache identity.

The check also confirms the explicit new user config path and the absence of a
self-authenticating administrator-policy claim.
