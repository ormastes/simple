# BuildRunner native Hello task

Authored manual; generated-doc verification remains pending a qualified runtime.
These fixture scenarios validate manifests and receipts, not live compilation.

1. Construct and round-trip a Hello manifest. Keep manager arguments separate
   from compiler arguments; select one-binary output and declare `hello.exe`.
2. Compare the cache key with the prior implicit-mode identity. The new task
   must not reuse that key.
3. Reject output traversal, a missing output declaration and an attempt beyond
   the configured retry budget. Retain the declared source input.
4. Admit only a matching success receipt. Reject stale attempt identities and
   failed receipts that claim output authority.
5. Change a runtime input digest. Both cache and immutable task identity change.

For live Darwin work, supply SDKROOT and MACOSX_DEPLOYMENT_TARGET as described
in the [guide](../../../../07_guide/tooling/buildrunner_stage_trace.md#native-hello-fixture-prerequisites).
Strict process ownership and enforced memory remain separate prerequisites.
