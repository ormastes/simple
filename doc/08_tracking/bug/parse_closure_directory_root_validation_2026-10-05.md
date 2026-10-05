# Parse-shard closure rejects valid directory selectors

Status: OPEN; source repair and regressions prepared, native verification pending.

## Observed failure

The full-CLI Phase 4 retry `early-p4-full-cli-62e85c-command-owners2`
used Phase 2 producer `2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`
(source `916be6c20617637e2cccf3d18c23669470ab8ffe`) against source
`62e85c139d93d822763c382839eeb46d9880d67d`. It stopped with compile exit 1:

`parse-shard closure publication rejected: entry-closure-root-invalid`

Its complete 292-byte log SHA is
`3d7e1f826be36bdfdecef4e4a3b6e5d583f70b2651c2206418943ba6f4cbf0b3`.
The watchdog recorded 3,241,888 KiB peak RSS, monitor-only/unlimited policy,
quiescent 1 and observer errors 0. The outer collector terminated one owned
remnant on root exit. No new HIR ledger, native cache-hit count, or executable
was produced; the predecessor's 2592/2593 HIR results cannot qualify this attempt.

## Proven source path

With parse shards enabled, `native_build_main` calls
`native_build_publish_parse_closure_v1`. The parent creates a binding using
`native_build_authority_source_roots_v1`, then passes it through
`compiler_entry_closure_publish_v1` to `native_entry_closure_binding_digest_v1`.
That function mistakenly applied `compile_source_inventory_path_valid_v1`
to each source root. The inventory validator requires `.spl` or `simple.sdn`,
so ordinary directory selectors fail unconditionally.

This packet supplies relative roots, including `src/compositions/kernel_llvm_cranelift`,
`src/compiler`, `src/app`, `src/lib`, `src/os`, `src/plugins`,
`src/package_ownership`, and `src/compositions`; the coordinator appends the
relative `src/app/cli/main.spl` entry. Explicit source arguments are preserved,
not secretly made absolute. The entry passed the earlier file validation.

The repair adds a dedicated canonical-relative root validator. It accepts
directory and file selectors while rejecting empty, dot, parent-traversal,
absolute/drive/backslash, delimiter, control-character, and empty-segment
spellings. Ordered root bytes still participate in the same length-framed
binding digest. Inventory-member and selected-file validators are unchanged.

`.` is not a legitimate selector here: the source authority admits finite
src/test families, and snapshot ownership rejects the checkout itself. Existing
absolute or `./` CLI selector normalization is a separate parse-request boundary
limitation: this patch does not change those spellings or weaken receipt identity.

## Verification

Four new unit cases cover the actual packet roots, safe UTF-8/file selectors,
unsafe roots, stable/distinct ordered binding digests, and continued rejection
of a directory as an inventory source row. Existing receipt selection tests
already construct directory-root bindings and remain applicable. All native
execution is UNRUN. Current Phase 2 and independent retry inputs are untouched.
No forced one-shard workaround or validator bypass is introduced.
