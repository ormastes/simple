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
