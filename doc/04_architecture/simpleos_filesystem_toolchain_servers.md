# Architecture: SimpleOS filesystem toolchain and servers

## Decision

Keep one owner per boundary:

```text
QEMU request -> boot TCP facade -> HTTP default or POST /db service
mounted VFS file -> executable range reader -> ELF PT_LOAD mapper -> user task
target Simple payload -> install image role list -> compiler/interpreter/loader paths
```

The loader opens the requested canonical path, reads the ELF header/program
headers, allocates pages, and fills each `PT_LOAD` range with bounded reads. It
does not cache or substitute executable bytes; the old global preload is outside
the hosted launch path.

The existing single HTTP listener remains the only network owner. `POST /db`
dispatches to one persistent bounded database service; all other requests keep
the existing HTTP response path. A second listener and scheduler are unnecessary
for the selected request/response proof.

The DB scenario uses existing Pure Simple parsing/storage primitives where the
freestanding closure supports them; otherwise its smallest owner-layer service
implements only the selected bounded create/insert/select protocol and is not
presented as the full historical `simple_db` product.

GOT residency remains an explicit bare-metal optimization. Hosted SimpleOS,
Clang, Simple compiler, interpreter, and loader all use filesystem provenance.

<!-- codex-design -->
## Stage 4 prerequisite: compact module surfaces

The filesystem goal depends on a current pure-Simple Stage 4 CLI. In the
low-memory Stage 4 entry-closure lane, parsing all rich Modules before HIR
lowering retains unbounded executable AST state. Replace that ownership with:

```text
source order
  -> parse one rich Module
  -> independently owned ModuleSurface index
  -> remove rich Module from retained state
  -> complete surface index
  -> parse/lower one rich Module to HIR at a time
  -> evict rich Modules, then source text and surfaces
  -> existing HIR-wide MIR layout/lowering
```

`ModuleSurface` is an explicit cross-module resolver value, never a
body-stripped `Module`. Its public contract is:

- `ModuleSurface`
- `ModuleSurfacesByName`
- `ModuleSurfaceCallable`
- `ModuleSurfaceComposite`
- `ModuleSurfaceEnum`
- `ModuleSurfaceTrait`
- `ModuleSurfaceImpl`
- `ModuleSurfaceConst`
- `module_surface_from_module`
- `hirlowering_for_module`
- `driver_streaming_surface_enabled`
- `module_surface_source_matches`
- `module_surface_trait_origin_key`

The surface retains imports/exports, declaration identity and visibility,
callable signatures, composite kind/name identity, impl headers and associated
types, constant declared types, enum variants, and trait declarations. Ordinary
function/method bodies, parameter defaults, and constant values are absent.
Two executable AST fragments remain intentionally: trait default-method bodies
and enum struct-field default expressions, because existing imported-trait and
imported-enum lowering consumes them.

Imported traits are keyed by canonical `module_name::trait_name`; a short name
or local alias is never the cache identity. Identical canonical imports are
idempotent; conflicting source fingerprints or declaration metadata fail.
Source order is always
`CompileContext.sources`, never dictionary iteration. Every surface records its
source index, canonical path/module, content length, and
`rt_hash_text(content)`; the streaming HIR pass fails closed on a mismatch.

The lane activates only for AOT + low-memory + entry closure +
`SIMPLE_BOOTSTRAP_STAGE4=1`, excluding VHDL. Check, interpreter, JIT, normal
bootstrap, non-low-memory, and VHDL behavior remain unchanged.

`ModuleSurfacesByName` is the single resolver contract for import, re-export,
glob, sibling, enum, and trait resolution across all HIR paths. Non-streaming
paths derive it from their retained rich modules without reparsing; only the
Stage4 gate changes ownership and reparses one module at a time.

### 2026-07-24 declaration-only Phase 2 addendum

Phase 2 uses the core parser's existing declaration path, with ordinary
top-level function bodies omitted before flat-AST conversion. It retains
imports/exports, callable signatures, composite identity, enum payloads and
defaults, traits and default bodies, impl headers and methods, and constant
declared types. The frontend returns a `Module`; the driver remains the owner
that converts it to `ModuleSurface`, preserving the frontend-to-HIR layer
boundary.

The first slice intentionally keeps class, trait, and impl method bodies on the
existing parser path. Non-Stage4 parsing, source fingerprints, diagnostics,
aliasing, and Phase 3 full parsing are unchanged. TreeSitter outlines are not a
substitute because they omit required trait default bodies.

The existing async desugar still runs on the bodyless Phase-2 module so exported
headers use the same `Future<T>` return and non-async flag as Phase 3.
Suspension-derived state enums and poll helpers are module-private and are
generated only by the full Phase-3 parse.
