# Privileged Host Import Admission

Status: **PROPOSED / RED**. The dedicated browser command-capability runtime import
does not exist on `origin/main`; this document freezes its compiler boundary
before any provider or caller is added.

## Scope

The first privileged row is:

| symbol | canonical physical owner | native only |
|---|---|---|
| `rt_browser_renderer_command_capability_new` | `src/os/hosted/hosted_browser_renderer_process.spl` | yes |

`rt_random_hex` is deliberately not privileged by this row. It already has
multiple legitimate declarations and consumers. `HostedOnly` is also not an
authorization class; ordinary hosted externs keep their existing behavior.

## Source identity

`src/compiler/35.semantics/privileged_host_imports.spl` owns the frozen
`PrivilegedHostImport` metadata and policy. Authorization consumes the
`ModuleSurface.canonical_path` produced by
`module_surface_canonical_path`; module names, import spelling, environment
state, and interpreter `CURRENT_EXEC_MODULE` are never principals.

The policy accepts the row only for the one physical source already admitted
by module-surface collision checking. A copied file, a second physical source,
an import/re-export, or an owner-name claim fails
`privileged-host-import-owner`. A lexical spelling such as `./src/...` is
accepted only after it normalizes to that already admitted canonical surface;
the spelling itself grants nothing. Symlink discovery must resolve to one
admitted physical surface and must not add a second requester object.

## Mandatory hooks

- `driver_hir_pipeline_passes.spl` rejects unauthorized declarations and
  imports before type checking or object emission.
- MIR call lowering rejects an unauthorized call even if earlier metadata was
  malformed or bypassed.
- entry-closure validation admits exactly one requester object for the row.
- native object metadata records symbol plus canonical owner identity.
- both interpreters reject the canonical owner with
  `privileged-host-import-native-only` before builtin, dynamic, or local
  lookup.
- Rust native discovery mirrors the same `PrivilegedRuntimeSymbol` row and
  validates source identity before parallel compilation; Rust object and
  entry-closure checks mirror the pure-Simple gates.

Provider identity, `dlsym`, JIT, runtime implementation, and browser command
issuance are separate changes and are not implemented by this contract.

## Frozen evidence

The future executable SSpec must use exactly these manual steps:

1. `Compile the canonical privileged owner`
2. `Reject a non-owner declaration`
3. `Reject interpreter execution`
4. `Preserve ordinary hosted externs`

It must additionally cover copied source, path/symlink aliases, import
re-export, duplicate requester objects in an entry closure, and a normal actor
extern. No active SSpec or generated manual exists while its imported compiler
policy module is absent. The gate remains RED until the dedicated symbol and
all compiler hooks exist.
