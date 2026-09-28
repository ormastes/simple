# Target 6 native CAS batch generation corruption

Status: open. This blocks production publication of warm package archives and
the persistent package/module index cutover.

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
