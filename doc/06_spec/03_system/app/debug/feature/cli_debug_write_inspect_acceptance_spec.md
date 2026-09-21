# Debug evidence write and inspect CLI acceptance

**Requirements:** REQ-DEBUG-EVIDENCE-CLI-001, REQ-DEBUG-EVIDENCE-CLI-002

The production `simple debug` command writes a Debug Evidence Bundle V1 from a
real artifact and then inspects the same retained bundle. Acceptance checks the
exact build ID and artifact count, byte and SHA-256 equality, and all six
normalized capabilities remaining `Unverified`.

## Scenario: round trip one artifact through the real production CLI

1. Prepare a unique source artifact and absent bundle root.
2. Bind an immutable pure-Simple runtime to its canonical admission receipt and
   verify both exact hashes, lineage, and version output.
3. Run `simple debug write` through that admitted runtime.
4. Verify the retained artifact equals the concrete fixture bytes and has a
   valid matching SHA-256.
5. Verify all normalized state capabilities remain `Unverified`.
6. Run `simple debug inspect` on that same bundle and verify its identity.

**Admission:** pending a pure-Simple runtime admitted for the general test/debug
CLI role and generated SPipe documentation. A Stage 2 compiler receipt alone,
a Rust seed, or a missing runtime cannot satisfy this scenario.

The initial native target mapping covers Windows MSVC, Linux GNU, and macOS.
Other native ABIs remain outside this acceptance slice until mapped explicitly.
