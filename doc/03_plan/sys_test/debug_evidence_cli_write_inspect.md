# Debug evidence CLI write and inspect acceptance

## Scope

This plan covers the OPEN P2 TODO at
`src/app/cli_debug/evidence_write_v1.spl`: exercise the production CLI boundary
for `simple debug write`, followed by `simple debug inspect` on the same bundle.

## Acceptance criteria

- **REQ-DEBUG-EVIDENCE-CLI-001:** An admitted immutable Simple executable writes
  one real artifact through `simple debug write`; the command exits zero and
  reports the exact bundle root and artifact count.
- **REQ-DEBUG-EVIDENCE-CLI-002:** `simple debug inspect` reads that exact bundle,
  exits zero, and reports its exact build ID and artifact count.
- Copied bytes and SHA-256 equal the source artifact.
- The normalized capsule explicitly leaves analyze, forward resume, exact
  replay, reverse execution, counterfactual fork, and profile correlation
  `Unverified`.
- A missing or seed-only runtime is a failed admission, never a skip or pass.

## Execution

Run with the exact runtime and its canonical provenance receipt bound by hash:

```text
SIMPLE_ADMITTED_RUNTIME=<immutable-pure-simple> \
SIMPLE_ADMITTED_RUNTIME_SHA256=<runtime-sha256> \
SIMPLE_ADMITTED_RUNTIME_RECEIPT=<simple-runtime-provenance-v1.env> \
SIMPLE_ADMITTED_RUNTIME_RECEIPT_SHA256=<receipt-sha256> \
SIMPLE_ADMITTED_RUNTIME_TARGET=<native-host-target-triple> \
<runner> test test/03_system/app/debug/feature/cli_debug_write_inspect_acceptance_spec.spl --mode=interpreter
```

The child has no implicit fallback. Before behavior, the test requires the
canonical `simple-runtime-provenance-v1` receipt, verifies both receipt and
runtime hashes, requires `status=admitted` and `implementation=pure-simple`,
binds the receipt target to the native host target supplied by the admission
runner, checks exact version output, and rejects Rust bootstrap seed diagnostics.
This first acceptance slice supports native Windows MSVC, Linux GNU, and macOS
target triples. Other native ABIs require an explicit target mapping before
they can enter this gate; they cannot silently pass as one of these targets.

## Current admission status

The executable acceptance remains pending until a pure-Simple runtime is
admitted specifically for the general test/debug CLI role. A Stage 2 compiler
receipt by itself is insufficient. Keep the source TODO and database row OPEN
until that role-scoped run and SPipe doc generation both succeed.
