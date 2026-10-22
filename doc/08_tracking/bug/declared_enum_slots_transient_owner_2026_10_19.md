# Declared enum slot metadata survives its module reset

Status: source fix and two regression scenarios authored; runtime UNRUN.

## Source-established lifetime gap

`HirLowering.register_declared_pattern_enum_slots` in
`20.hir/hir_lowering/_Expressions/expression_components.spl` creates dynamic
owner/variant keys and `HirDeclaredPatternEnumSlots` with nested HIR type arrays.
`_Items/module_build.spl` registers these slots during module lowering.
The retained lowerer's 49 phase memo promotion roots deliberately exclude
this module-local map.

`80.driver/driver_hir_pipeline_lowering.spl` pauses a completed shard's arena,
promotes retained roots, calls `begin_module`, and reclaims the arena.
The additional explicit slot-map clear is conditional on an archive input.
The common `begin_module` previously omitted this map, leaving non-archive
shards' retained lowerer pointing into reclaimed storage. Numeric symbol IDs
also restart at module reset, so stale keys must not survive that boundary.
This establishes a dangling owner and reset-contract violation, not an
observed post-free dereference.

## Fix and prevention

Clear `declared_pattern_enum_slots` alongside the other module-local enum maps
in `context_helpers.spl::begin_module`. Do not promote the map, retain module
body graphs, or change cache acceptance/fallback policies. Existing
archive-only compensating clears remain harmless and are outside this patch.

`test/01_unit/compiler/hir/declared_enum_slots_scope_cleanup_spec.spl` exercises
real parser declarations and the real slot-registration method. One case
checks detachment while the arena is paused, before reclamation; another
proves that a reused numeric symbol ID cannot inherit the previous key.
The corresponding manual records the unexecuted negative control and limits.

## Evidence boundaries and separate open issue

The retained b768 runner r1 log at
`build/codec-semantic-trust-root-20261019/retained-test-runner-20261019-r1/compile.log`
under the frozen producer tree ends with `body archive publication refused`
and exit 1. It does not establish an OOM or connect this reset defect to that
refusal. Historical Phase3 SIGSEGV and cache-off retained-path memory growth
remain unattributed; retained success paths that do not reset before scope
end are outside this narrow fix.

Separate OPEN source cost: `hir_body_archive_store_in_owned_scope_v1` encodes a
whole module for its digest, then `hir_cache_store_in_owned_scope` encodes it
again while the first blob is still live in the same scope. This establishes
duplicate encoding and overlapping blob storage, without proving a runtime
peak or causing r1's refusal. No change to that owner is included here.

Bug database registration remains pending the qualified repository tool; no
checksum-managed database rows were hand-edited. Frozen producer439, candidate
objects, execution caches and sibling TLDR changes are untouched.
