# env_get resolves to the wrong co-compiled definition on the seed

Status: OPEN. Severity: P1. Date: 2026-10-31.

## Symptom

On the Phase 1 seed interpreter, `env_get` imported as `-> text` can return the
result of `std.nogc_sync_mut.sffi.system_env_core.env_get`, which is `-> text?`.
Nothing fails at the call. The value is just wrong:

- `use std.io_runtime.{env_get}` gave a path beginning `Option::Some(D:/...`, so
  `file_hash_sha256_or_empty` returned empty.
- An unset variable gave nil, not `""`, so `value == ""` was false.

The seed warns about it: `public function env_get has 5 co-compiled definitions
with 2 differing signatures`.

## Reproduction

```text
use nogc_sync_mut.database.codec.sqlcipher4.{Sqlcipher4Error}
use std.nogc_sync_mut.io.env_ops.{env_get}
```

With both imports, `env_get("UNSET_NAME") == nil` is true. Without the first, the
result is `""`. Seed SHA-256:
`55be5e48ecd717a59cd7f0538768b22bbc832669025571c546d30fdf817dc0ec`.

## Fixed so far

`secret_ref_resolve` and the `fresh_secured_db` fixture use `env_get_opt`, which
has one definition.

## Not fixed

Other `env_get` callers remain exposed. Renaming the `text?` definitions to
`env_get_nilable` cleared the reproduction on the seed, but was reverted before
landing. It also reaches `src/lib/nogc_async_mut/sffi/system.spl`, wildcard
facades including `src/compiler/70.backend/sffi.spl`,
`scripts/audit/system-sffi-authority.shs` and `scripts/check/rt_alias_map.sdn`,
and needs a compiler build to verify. A proper fix binds a `use` to its named
module instead of a co-compiled name.

Related: `src/lib/nogc_sync_mut/desktop/lifecycle.spl:30` compares a `text?` value
with `""`, so an unset `XDG_RUNTIME_DIR` builds a bad lock path.

**Revalidated 2026-11-02: still plausible because OPEN. Severity: P1. Date: 2026-10-31; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 update: fix implemented, verification pending (full seed)

Root cause narrowed. The seed INTERPRETER already honours `use` bindings
(`import_bound_candidate`, 2026-08-31) and was re-checked correct on direct,
aliased and `export use` facade imports. The wrong body was chosen in the
flattened HIR/JIT lane: `Lowerer::resolve_flatten_owned_callable`
(`hir/lower/lowerer.rs`) looked up the caller's import bindings only when the
caller had a flatten owner, but the ENTRY module's imports are recorded under
the `<entry>` importer (as `resolve_flatten_owned_global` already handled). So a
bare `env_get(...)` from the entry module bound to the last-registered
definition. Repro before: `scratchpad` fixtures mod_a (`-> text`) / mod_b
(`-> text?`), `fn main` importing `mod_b.{env_get as bb}` and `mod_a.{env_get}`
printed `b=A` (wrong).

Fix: resolve entry-module callers through the `<entry>` binding table.
Regression test (failed before, passes after):
`mir::lower::tests::seed_regression_tests::entry_module_use_binding_selects_import_among_differing_signature_duplicates`.
NOT changed: ambiguous no-binding collisions stay a warning, not a hard error;
373 such collisions exist in a single spec run today, so an error would break
the stdlib (tracked in duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09).
Verification pending: end-to-end rerun of the fixtures on a redeployed seed.
