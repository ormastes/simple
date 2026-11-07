# Reverse-reference receipt ordering and publication

**Status:** AUTHORED / NOT_RUN. This manual describes five executable scenarios in [the spec](../../../../../test/01_unit/compiler/cache/reverse_reference_sort_equivalence_spec.spl). It is not a runner result or a generated-document validation receipt.

The production receipt owner now sorts ordinary NUL-free inputs through the canonical ordering helper and reuses encoded bytes for the publication digest. These scenarios compare actual production output against a preserved historical insertion-order oracle. They protect serialized compatibility; they do not measure throughput or qualify a full compiler build.

## Compare provider ordering

1. Select empty text, ASCII prefixes, accented Latin, Greek, CJK and emoji values.
2. Compare every pair using the canonical text comparator and the active provider’s ordinary text comparison.
3. Require identical less-than results for every pair.

This is provider-specific execution evidence when run. One provider’s result cannot qualify all platforms.

## Preserve duplicates and multibyte receipt bytes

1. Construct ten unsorted projection rows, including duplicate `aa`, multibyte names and family marker strings.
2. Encode through the production receipt owner and independently through the historical-order oracle.
3. Require byte-for-byte identical output, an exact `sha256:` digest of those bytes, and ten retained projections.

## Preserve NUL equal-prefix compatibility

1. Build `a NUL z` and `a NUL a` from explicit byte arrays using the production byte-to-text conversion.
2. Check the carrier length and bytes before testing the sort, preventing a truncated fixture from producing a false pass.
3. Include duplicate NUL-bearing rows and ordinary names; require the production encoded receipt to equal the historical-order bytes.

The control preserves the active provider’s legacy NUL ordering. It does not require different providers to assign identical ordering to embedded NUL.

## Preserve empty and invalid inputs

1. Encode an empty generation and compare its header/body with the historical oracle.
2. Try empty, newline-containing and carriage-return-containing consumer names.
3. Require both encoding and digest to return empty text for each invalid receipt.

## Publish the exact digest-addressed bytes

1. Create a process-specific temporary cache path and a real receipt containing duplicates and multibyte text.
2. Publish through the production generation owner.
3. Read `CURRENT` and require the exact tagged digest of the expected receipt.
4. Read the digest-addressed receipt, require the expected bytes, and verify the pointer/body match through the production helper.
5. Require successful removal of the temporary fixture directory.

Publication uses real filesystem operations. Missing pointer/body data fails assertions; it is not an accepted skip. The PID-based fixture assumes the coordinator serializes this spec and owns its temporary namespace; it is not a hostile same-user isolation test.

## Execution and remaining qualification

An admitted source-matched full CLI must run this exact spec once under the campaign’s canonical process-tree watchdog, with retained logs, nonzero discovery, five executed scenarios and no skipped requirement. The finite execution manifest assigns 120 seconds and a single native slot. Do not rerun an unchanged green result.

The separate cardinality spec and production performance probe cover other obligations. No runtime, branch-coverage, latency or RSS PASS is claimed here.

After runtime admission, validate this manual using the real `spipe-docgen` command for the spec with `--output doc/06_spec --no-index`; require complete documentation and `0 stubs`. Docgen is **NOT_RUN** and manual acceptance remains pending.
