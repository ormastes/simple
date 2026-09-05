# Versioned Dynamic Optimizer Manifest — Design

## Overview

The dynamic optimizer manifest lets external plugin passes declare themselves
to the Simple compiler's MIR optimization pipeline without recompiling the
compiler.  A manifest file (`.sdn` or `.json`) describes which passes a plugin
provides, what ABI version they target, what capabilities they require, and how
to load them.

The built-in pass inventory (declared in `mir_opt/mod.spl`) always takes
precedence over dynamic passes on hot paths, as established in the
"built-in optimizer rules should precede dynamic loading" principle.

---

## Manifest File Format (v1)

Manifests are Simple SDN files with the `.opt-manifest` extension (or `.json`
for interop).  The top-level structure:

```
schema_version: 1
compiler_abi: "simple.opt.mir.v1"
name: "my-crypto-passes"
version: "0.3.1"
min_compiler_version: "0.9.0"
passes:
  - stable_name: "my_aes_fold"
    aliases: ["aes_fold"]
    scope: "module"
    capability_requires: ["x86.aes", "x86.pclmul"]
    contract:
      inputs: ["typed_mir"]
      outputs: ["canonical_mir"]
      purity: "pure"
    entry_symbol: "my_aes_fold_run_on_module"
```

### Required Fields

| Field | Type | Description |
|---|---|---|
| `schema_version` | int | Must be `1` for this spec |
| `compiler_abi` | text | ABI contract: `"simple.opt.mir.v1"` |
| `name` | text | Human-readable plugin name |
| `version` | text | Plugin SemVer |
| `min_compiler_version` | text | Minimum Simple compiler version |
| `passes` | list | One entry per pass exported |

### Per-Pass Fields

| Field | Type | Description |
|---|---|---|
| `stable_name` | text | Canonical name — must be unique across all loaded manifests |
| `aliases` | list\<text\> | Alternative names; must not conflict with built-in aliases |
| `scope` | `"function"` \| `"module"` | Whether pass is per-function or whole-module |
| `capability_requires` | list\<text\> | Target capability flags required (empty = always available) |
| `contract.inputs` | list\<text\> | Expected MIR state before pass |
| `contract.outputs` | list\<text\> | Guaranteed MIR state after pass |
| `contract.purity` | text | `"pure"` \| `"side_effects"` |
| `entry_symbol` | text | Exported symbol name in the shared library |

---

## Versioning and Compatibility Rules

### ABI versioning

`compiler_abi` is checked at load time.  The format is `"simple.opt.mir.vN"`.
A compiler at major ABI version N will refuse to load a manifest declaring
version N+1 or higher.  ABI version N is backwards-compatible with manifests
declaring version N-1 as long as the entry symbol signatures match.

### Stable-name conflict rules

1. Built-in stable names (registered in `mir_pass_descriptor_registry()`) are
   reserved and cannot be overridden by dynamic manifests.
2. A manifest that declares a `stable_name` already present in the built-in
   registry is rejected with `ManifestError.StableNameConflict`.
3. Alias conflicts with built-in aliases are rejected with
   `ManifestError.AliasConflict`.
4. Among dynamic manifests, first-loaded wins; subsequent conflicting names
   emit a warning and the conflicting pass is skipped.

### Capability gating

If `capability_requires` lists any flags, the pass is silently skipped when
those flags are not set in the active `TargetOptContext.caps_kind`.  This
matches how `pipeline_optimize` gates `pattern_idiom` and `auto_vectorize`.

---

## Load Flow

```
load_manifest_v1(json_text: text) -> Result<OptimizerManifest, ManifestError>
  parse schema_version → reject if != 1
  parse compiler_abi   → reject if incompatible
  for each pass entry:
    reject if stable_name in built-in registry
    reject if alias in built-in alias set
    construct DynamicPassDescriptor
  return OptimizerManifest
```

After a manifest is loaded, `pipeline_optimize` merges dynamic descriptors
into the dispatch table for that compilation session.  Dynamic passes are
always placed after built-in passes of the same level.

---

## Integration with PassKind / PassScope

Dynamic passes do not get a `PassKind` enum variant (that is a closed set of
built-in passes).  Instead, `DynamicPassDescriptor` carries a `stable_name`
and `scope` field directly, and dispatch uses a separate dynamic branch in
`run_pass_on_module` after the main `PassKind` match.

```
fn run_pass_on_module(pass_name, module):
    val desc = mir_pass_descriptor_for_name(pass_name)
    if desc.?:
        return run_typed_pass_on_module(desc.unwrap().kind, module)   # built-in
    val dyn_desc = dynamic_pass_registry_lookup(pass_name)
    if dyn_desc.?:
        return run_dynamic_pass_on_module(dyn_desc.unwrap(), module)  # dynamic
    return module  # unknown pass
```

This ensures the typed-runner hot path is not polluted with dynamic dispatch
overhead for built-in passes.

---

## Skeleton Types (see `optimizer_manifest.spl`)

- `ManifestSchemaVersion` — enum for supported schema versions
- `ManifestPassEntry` — per-pass descriptor parsed from manifest file
- `OptimizerManifest` — validated, loaded manifest ready to register
- `ManifestError` — parse and validation error variants
- `DynamicPassRegistry` — session-scoped registry of loaded dynamic passes
- `load_manifest_v1(json: text) -> Result<OptimizerManifest, ManifestError>`
- `dynamic_pass_registry_new() -> DynamicPassRegistry`
- `dynamic_pass_registry_register(registry, manifest) -> Result<(), ManifestError>`
- `dynamic_pass_registry_lookup(registry, name) -> DynamicPassDescriptor?`

---

## Future Work

- Schema version 2: add `pipeline_position` hints (`before:dce`, `after:inline`)
- Schema version 3: add `invariant_preserves` for formal correctness annotations
- Hot-reload: re-read manifest on file change without restarting the compiler
- Sandboxed evaluation: run dynamic passes in WASM sandbox for safety
