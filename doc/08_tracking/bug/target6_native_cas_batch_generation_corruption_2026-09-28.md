# Target 6 native CAS batch generation corruption

Status: candidate repair in `codex/target6-cas-publication-guard-20260928`.
The full compiler/index cutover remains open.

## Reproduction

An entry-closure, no-stub Stage2 native spec published one real package archive
through `package_archive_publish_scc_v1`. Publication returned success and
created `batch-v1/CURRENT`, a transaction, and a valid looking package/action
mapping. `package_archive_load_v1` immediately returned `archive-missing` for
the same aggregate entry and authority. The generation file held only the
three bytes `b6 15 0a`; it contained neither its schema header nor the
mapping. The transaction manifest and mapping file contained their expected
text. A test that continued to pin the absent receipt crashed; that test
control-flow error does not explain the malformed generation.

The native build compiled 94 source units with zero failures. A trial change
that built the generation text by sequential concatenation also linked, but
its runtime process ran for over a minute, reached about 34 GiB RSS, and was
terminated without a test verdict. The trial was reverted. The retained
manifest producer/decoder round-trip spec passes 2/2; it does not exercise
CAS batch publication.

## Required repair

1. Identify why `cas_batch_publish_v1` serializes a truncated generation on
   the admitted native compiler; the current chained array concat/join is a
   candidate, not a proven cause. Isolate a bounded native reproducer before
   changing the production serializer again.
2. Reject a malformed or unreadable generation before publishing `CURRENT`.
   Validate exact header, transaction identity, and complete package mappings
   from the persisted file.
3. Run a fail-fast native publish -> load -> pin -> decode scenario for zero
   and nonzero dependency counts. Then resume the typed cold graph publisher
   and native time/RSS cohort. Do not treat the manifest-only pass as a warm
   route or Target 6 completion receipt.

## Candidate repair evidence

A one-unit no-stub Stage2 native reproducer returned zero bytes for
`[header...].concat([]).concat([mapping]).join("\n")`; direct, pushed-array,
string-concatenated, and interpolated equivalents returned the expected 98
bytes. This identifies the chained array concat/join as a concrete native
failure. The CAS writer now pushes each line and uses the runtime text builder
through a checked helper. It reads the persisted generation before sealing or
publishing `CURRENT` and rejects a mismatch, header/transaction mismatch, or
missing mapping line.

The first archive round-trip probe crashed in `path_join` from the manifest's
`[text].join(",")` call. The candidate replaces ambiguous text-list joins in
the CAS/archive path with an explicit checked text-builder helper. A 70-unit
no-stub Stage2 native build then passed a fail-fast two-generation
publish/load/pin probe: zero dependencies produced a 328-byte generation,
and one dependency with an inherited mapping produced 525 bytes. Runtime was
0.05 seconds with 2,136 KiB peak RSS under a 4 GB address-space bound.
These focused results do not prove the full CLI or production warm route.
