# Cosmos FTL pure-policy evidence

Scope is limited to the scalar policy extracted from `cosmos_ftl.c`.
Pointer/table acquisition, callbacks, writeback ordering, and device effects
remain in C.

## Allocator reserve boundary

Candidate scans call `cosmos_ftl_policy_allocate_page_action` with
`free_count_is_final = 0`.  The policy returns `ACTION_TRACK_FREE`, allowing
the C bridge to preserve its historical candidate count and first-free-block
side effects.  After the scan, the bridge makes one final call with the exact
count and `free_count_is_final = 1`.

For ordinary allocation the final decision is `ACTION_USE_FREE` only when
`free_count > 409`; exactly 409 therefore returns `ACTION_TRACK_FREE`, and the
bridge returns `COSMOS_UNAVAILABLE`.  GC uses reserve zero and may consume a
non-empty free pool.

## Evidence gates

- `scripts/check/check-cosmos-ftl-policy-source-c.shs` is a non-release
  diagnostic.  It validates the pinned 41-export/185-decision source ledger,
  the exact 409/410 allocator boundary, the frozen-C bridge contract, and
  clang/llvm-cov coverage of all 352 frozen-oracle branch edges.  It writes no
  receipt and makes no Simple execution-coverage claim.
- `scripts/check/check-cosmos-ftl-policy.shs` is the release evidence gate.  It
  fails closed before evidence work unless `SIMPLE_STAGE4_BIN` names an
  admitted current-tree pure-Simple compiler with adjacent valid provenance.
  It compares all 41 function output rows and four allocator-mode rows with
  the independent frozen C oracle, maps compiler/runtime coverage rows to
  `COSMOS-FTL-D001..D185`, rejects extra owner rows, and requires all 370
  named outcomes.  The last three decisions name the CRC loops previously
  omitted from the denominator.  The gate independently pins and requires
  41/41 frozen-C functions, 278/278 lines, and 352/352 LLVM branch edges, and
  retains the instrumented binary, merged profile, and text report used for
  that result.  It also checks host/ARM C ABI and object closure.

The Rust bootstrap seed may be used only for explicitly diagnostic parity.  A
Rust-seed run cannot produce the Stage4 receipt or satisfy the named Simple
outcome gate.
