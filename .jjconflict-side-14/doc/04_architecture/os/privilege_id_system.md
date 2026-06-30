# Privilege ID System

**Status:** landed in `spm-winfs-llm-suite` (2026-04-18).

## Concept

Hierarchical string ids with a runtime intern handle. A granted id prefix-matches every more-specific id. Users subdivide ids under paths they already hold; groups are named sets of ids expanded at check time.

```
id.user.banking             # coarse
id.user.banking.view        # read-only sub-scope
id.user.banking.transfer    # sensitive sub-scope
id.group.dev                # a named set; members expanded at check
```

## Types

`src/lib/common/privilege/id_path.spl`
```
class IdPath { segments: [text], intern_id: u32 }
fn id_path_intern(s: text) -> IdPath
fn id_path_prefix_match(granted: IdPath, required: IdPath) -> bool
fn id_path_subdivide(parent: IdPath, child: text) -> Result<IdPath, Error>
```

`src/lib/common/privilege/authority_token.spl`
```
enum AuthorityLevel { Public, Internal, Sensitive, Secret }
enum Scope { Process, Session, OneShot }
class AuthorityToken {
    id_path: IdPath
    level: AuthorityLevel      # NOTE: field is "level" (not "authority")
    principal: Principal
    trust_source: TrustLevel   # aliased from app.package_registry.trust
    scope: Scope
    issuer_sig: [u8]
}
```

`src/lib/common/privilege/store.spl` — pure; returns new instances on mutation.
`src/lib/nogc_sync_mut/privilege/store_fs.spl` — SDN save/load at `~/.simple/privileges.sdn`.

## Relation to existing `PrivilegeMask`

SimpleOS kernel already has a bitmap `PrivilegeMask` + `sys_privctl` in `src/os/kernel/types/capability_types.spl`. These **coexist** — no collision, no replacement:

- `PrivilegeMask` is a kernel-local coarse bitmap used by the existing capability gate.
- `AuthorityToken` + `IdPath` live in userland (`src/lib/common/privilege/`).
- The kernel never imports the userland privilege module. Instead, `src/os/kernel/privilege/privilege_bridge.spl` defines `PrivilegeTokenMirror` as plain bytes; userland serializes an `AuthorityToken` into that mirror and kernel IPC does a two-gate check: `CapabilitySet.check` **AND** `privilege_bridge.two_gate_check`. Both must pass.

This preserves MDSOC: kernel stays kernel-only.

## Lookup semantics

```
PrivilegeStore.lookup(principal, required) → Option<AuthorityToken>
```
Returns the narrowest granted token whose `id_path` prefix-matches `required`. Groups are expanded first via `expand_groups`. Revoked tokens (by `issuer_sig`) are filtered out.

## Subdivide

Only a holder of `id.X` may mint a child `id.X.Y`. Authority level of the child is `<=` the parent's.

## Notes on reuse

- `TrustLevel` enum already existed in `src/app/package.registry/trust.spl` (`RegistryTrusted, UserTrusted, Untrusted, Revoked`). We alias it as `TrustSource` in docs; the type is not redefined.
- Intern table is module-local. Two calls with the same segments produce the same `intern_id`.
