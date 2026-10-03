# Package index reader acquisition transaction

Source: `test/01_unit/compiler/cache/package_module_index_reader_transaction_spec.spl`.
Requirement: `PSI-REQ-004`. Status: UNEXECUTED; reader implementation present.
This hand-maintained manual is not generated execution evidence.

## Refuse contended acquisition, then admit after release

1. Publish a complete generation through the production owner.
2. Hold `CURRENT.lock` using a separate OS handle and call the production reader.
3. Release the handle before checking results. Expect an invalid result with
   `generation-lock-unavailable`, empty digest and no decoded generation.
4. Read after release. Expect an admitted digest and exact canonical generation
   bytes. The current unlocked reader is expected to violate step 3; actual
   baseline execution must still capture the actual pre-fix failure.

## Preserve an owned generation after file collection

1. Publish A, acquire its decoded value and capture canonical bytes.
2. Publish B and collect the unretained A file.
3. Expect A's file absent, the owned A value unchanged, and the current reader
   admitting B. This tests owned in-memory lifetime, not an archive lease.

## Preserve missing-storage compatibility

1. Remove the isolated fixture root and read CURRENT.
2. Expect `missing-or-invalid-generation` and no cache directory created.

Required follow-up: execute baseline/candidate with admitted runtime provenance,
regenerate this manual, and run process-barrier publication/reader/GC coverage.
No unit assertion alone certifies the full concurrency or performance matrix.
