# Separate bootstrap tool and compiled-source authority

The retained `run-bootstrap-test-wave.py` callback accepts `--tool-root`,
`--tool-manifest`, and `--tool-manifest-sha256`. Its `--source-root` remains
the immutable source supplied to the compiler and canonical test inventory.
Use this when reviewed orchestration fixes postdate the frozen source epoch.
Never claim these script changes exist in that source commit.

The tool manifest has schema `simple-bootstrap-tool-code-v1`, a `tool_head`
Git commit, and a `files` object mapping relative paths to SHA-256 digests.
It covers every physical file in `scripts/bootstrap/` and `scripts/check/lib/`
(excluding Python bytecode caches). Store the manifest outside those trees.
The parent request must pin the manifest, executing callback, validator, Python,
and shell before invocation. Materialize the tool closure from the reviewed
commit; do not borrow mutable scripts from an unrelated working tree.

The callback records both roots, source and tool commits, manifest hash, and
the explicit inherited tool-authority environment. Synchronous child owners
resolve orchestration scripts, Perl modules, and provenance facades from the
tool root. Source inventory, source snapshots, compiler arguments, test cwd,
and generated product source continue to use the source root. The tool tree
is verified before work and before successful terminal publication; changed
or incomplete closures fail infrastructure validation. Resuming with separate
tools requires the original tool manifest identity.

This does not grant generated-source admission, qualify a compiler, waive
registry verification, or make a diagnostic matrix a full-suite PASS. The
canonical generated-root admission and producer gates still apply. Native
six-product execution remains unqualified until those gates and real receipts
complete.

The retained callback consumes one canonical 40-slot reservation: Phase1 uses
20 and the sequential six-product owner uses 20. Products may build, enumerate,
and run their first authentic case before Phase1 terminates. Full fresh-suite
execution waits for the exact Phase1 terminal receipt; failure is preserved
but does not block collecting independent product results.
