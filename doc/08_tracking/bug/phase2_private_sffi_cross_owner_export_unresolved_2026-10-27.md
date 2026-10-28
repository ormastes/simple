# Phase 2: private SFFI helper imports reach the linker undeclared

Canonical ID: `phase2_private_sffi_cross_owner_export_unresolved_2026-10-27`.
Status: open; public-owner facade workaround authored, compile retry pending.
Severity: build-blocking. DB reconciliation pending: no admitted full CLI is
available to update the authoritative bug DB in this lane.

## Observed subject and failure

The parent session's user-requested Phase 2 compile-only attempt failed at link
for source `bd7ce676d81a2befaba3ad1b645f0e7d2dc27d5b` in
`/tmp/simple-scv-implementation-wave1-20261027`. Its bootstrap-only producer was
`/tmp/simple-scv-runtime-producer-20261027/build/bootstrap-cranelift/stage3/aarch64-unknown-linux-gnu/stage2-runtime-authority/simple`,
SHA-256 `ea710ff69ddec7c2ad6d1ba3528231bf5461b6e4438c3aaeb586cd731f287cee`.
The producer role is `rust_seed_bootstrap_only`; this is build diagnosis, not
runtime admission or acceptance evidence.

The preserved log is `/tmp/scv-phase2-current-20261027/compile.log`, SHA-256
`13ed2a9f673733738285947d0104db80e1771dce92c0d3f2d78c2ff0cd1f1aa2`.
It identifies exactly seven undeclared globals: `_sffi_env_get`, `_sffi_env_set`,
`_sffi_exit`, `_sffi_stdout_flush`, `_sffi_transient_array_scope_begin`,
`_sffi_transient_array_scope_pause`, `_sffi_transient_array_scope_end`.
Attribution points to the split selected, streaming and retained parser owners.
The compiler reports that HIR resolution returned nothing and `lenient_types`
lowered each missing identifier to a global. Link then fails on those globals.

## Boundary and bounded diagnosis

The helpers were private `@always_inline fn` definitions in
`driver_source_parse_support.spl`, listed in explicit `export` statements and
consumed through `use ...driver_source_parse_support.*`. The same owner's local
calls and other support imports are not in the unresolved set. This establishes
an unsupported private-inline/wildcard export boundary for this producer; it
does not isolate underscore naming, inline metadata, export handling or their
interaction as the compiler root cause. No Rust seed code is changed here.

## Workaround and retirement

Recovery commit for the original split: `7d3126f8608fd430b6f50de4f9c7487ba9b2a02c`.
Introduce normal `pub fn driver_parse_*_v1` owner facades calling the existing
same-module private aliases. Consumers explicitly import the public facades.
Arguments, return/null behavior, ordering and underlying FFI call count remain
unchanged; no extern declaration is copied into a consumer. The affected blocks
carry this canonical ID. The workaround commit is the commit introducing this
report; the parent records its exact SHA with the retry receipt.

Authored regression:
`test/01_unit/compiler/driver/source_parse_public_boundary_spec.spl` checks the
public owner boundary and absence of private aliases/duplicated externs in
consumers. It has not been executed. The decisive retry is the parent's same
Phase 2 compile-only command using its compatible private cache. Acceptance
execution remains deferred by the user until Phase 3 is ready.

Background fix owner: compiler import/export and inline admission. Keep this
bug open until an isolated original-form producer regression demonstrates that
private inline helpers cross an explicitly exported module boundary correctly.
Retire only the linked workaround after that root fix and compatible producer
evidence; a successful public-facade build does not prove the language bug fixed.
