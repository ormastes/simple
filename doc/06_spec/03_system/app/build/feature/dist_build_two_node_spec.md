# Distributed build: issued two-node qualification

**Requirements:** REQ-002, REQ-003, REQ-004, REQ-014  
**Evidence class:** live-host when provisioned; source-contract for missing-native rejection  
**Executable source:** `test/03_system/app/build/feature/dist_build_two_node_spec.spl`  
**Status:** Authored manually; SPipe docgen and runtime execution are pending the current test-runner repair and a provisioned Linux OCI fixture. A skipped live scenario is not a PASS.

## Operator scenario

1. Provision two distinct authenticated Linux OCI workers and a dedicated, empty owner for a cold two-action producer/consumer graph under the administrator-owned issued graph root. Keep the raw diagnostic controller outside the credential boundary.
2. Build and install the exact `simple_dist_build_issued_graph_parent` native executable. Record its SHA-256 independently of the graph and set `SIMPLE_DIST_QUAL_NATIVE` and `SIMPLE_DIST_QUAL_NATIVE_SHA256`.
3. Set `SIMPLE_DIST_QUAL_ISSUED_RECORD` to the content digest of the approved record. Set producer/consumer action and worker IDs using `SIMPLE_DIST_QUAL_PRODUCER_ACTION`, `SIMPLE_DIST_QUAL_CONSUMER_ACTION`, `SIMPLE_DIST_QUAL_PRODUCER_WORKER`, and `SIMPLE_DIST_QUAL_CONSUMER_WORKER`.
4. Set `SIMPLE_DIST_QUAL_PRODUCER_OUTPUT`, `SIMPLE_DIST_QUAL_PRODUCER_OUTPUT_SHA256`, `SIMPLE_DIST_QUAL_CONSUMER_OUTPUT`, and `SIMPLE_DIST_QUAL_CONSUMER_OUTPUT_SHA256` from independent fixture expectations. Run the executable SSpec through the deployed pure-Simple SPipe runner as an unprivileged operator.
5. The driver probes nonce-bound SSH capabilities on both workers, requires Linux OCI, copies the approved native bytes into a private directory and hashes that copy, then runs the cold issued graph. It requires this controller's two `PROPOSED` attempt IDs to match the accepted durable attempts, verifies two distinct accepted workers, checks the consumer dependency against the retained producer manifest and CAS bytes, verifies the consumer's retained output and both cleanup acknowledgements, then runs the same issued graph again and requires unchanged durable attempt and accepted counts.

Missing native bytes, record, credentials, worker capability, acceptance, CAS object or cleanup acknowledgement produce `BLOCKED`. The live scenario can report `PASS` only after both native executions and the durable audit. The source-contract scenario checks that an absent native controller is blocked. This manual does not yet prove staged compile-to-link execution, executable behavior, fault injection, cross-OS workers, numerical NFRs, or complete REQ-004/REQ-014 coverage.
