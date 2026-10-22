# Whole-graph issued route still needs native qualification

**Status:** Source implemented, qualification open. **Owner:** distributed scheduler S/C lanes; final reviewer Astra.

The dedicated graph record, protected `graph-plans` store, issuer preflight,
restricted graph entrypoint and `bin/simple_dist_build_graph_parent` wrapper
are implemented in source. Astra's read-only review found no scoped P0/P1.
The raw graph CLI still accepts diagnostic arguments and must remain outside
privileged credentials and installed release paths.

The Linux-only `scripts/check/check-dist-issued-native.shs` now prepares
private, hash-recorded candidate binaries from clean committed source and an
admitted Stage 4 compiler. Its receipt explicitly says unqualified. It has
not run on a prepared Linux host and does not install or authorize binaries.

**Unblock:** Authenticate independently supplied approval, install and protect
the administrator root and referenced file ancestors, isolate credentials,
build the exact native graph and staged controllers with the self-hosted
runtime, run the new focused specs, and qualify real two-node graph and
producer/link fixtures. No current runtime or end-to-end PASS is claimed.
On a prepared Linux host, start with
`sh scripts/check/check-dist-issued-native.shs <Stage-4-binary> <adjacent-Stage-4-provenance>`;
retain the candidate receipt and logs for the final reviewer.
