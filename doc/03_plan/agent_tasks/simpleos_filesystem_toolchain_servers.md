# Agent plan: SimpleOS filesystem toolchain and servers

| Lane | Result/owner |
|---|---|
| Server history/runtime audit | lower-model sidecar; complete, merge by root |
| LLVM/Clang FS audit | lower-model sidecar; complete, merge by root |
| Simple role/image audit | lower-model sidecar; complete, merge by root |
| Loader and image implementation | root; coordinate with active x86 FS lane |
| HTTP/DB implementation | root; existing TCP/service owners only |
| Generated manuals | root |
| Final review | normal/highest-capability root `$verify` |

Shared interfaces are the mounted VFS range reader, existing ELF mapper/spawn,
boot TCP facade, and centralized image role paths. Manual helper names and
fail-fast policy are recorded in
`.spipe/simpleos_filesystem_toolchain_servers/state.md`.

<!-- codex-design -->
## 2026-07-24 Stage 4 prerequisite lanes

| Lane | Owner | Deliverable |
|---|---|---|
| Surface model/extractor | lower-model sidecar | Explicit surface field map; no fake `Module` |
| Streaming driver | lower-model sidecar | Ordered two-pass state machine and activation matrix |
| HIR resolver migration | lower-model sidecar | Import/re-export/sibling/enum/trait/impl consumer map |
| RED tests and slope gate | lower-model sidecar | Unit, native four-file fixture, event-driven checker |
| Merge/implementation | root Codex | Minimum coherent compiler diff |
| Final architecture/code/manual review | highest-capability Codex | Accept/reject before Stage2/3 or done mark |

Frozen interfaces:

- `ModuleSurface`, `ModuleSurfacesByName`
- `ModuleSurfaceCallable`, `ModuleSurfaceComposite`, `ModuleSurfaceEnum`
- `ModuleSurfaceTrait`, `ModuleSurfaceImpl`, `ModuleSurfaceConst`
- `module_surface_from_module`, `hirlowering_for_module`
- `driver_streaming_surface_enabled`, `module_surface_source_matches`
- `module_surface_trait_origin_key`
- `phase2:surface:file:released`

Frozen test helpers:

- `module_surface_fixture_source`
- `write_surface_contract_module`, `write_surface_provider_module`
- `write_surface_facade_module`, `write_surface_entry_module`
- `compile_surface_native_fixture`, `run_surface_native_fixture`
- `collect_surface_release_markers`, `assert_surface_release_slope`

Temporary implementations must call `fail(...)`; no TODO or marker-only pass.

### 2026-07-24 declaration-parser lane

| Lane | Owner | Deliverable |
|---|---|---|
| Top-level body omission | lower-model sidecar | Reviewed parameter-threaded parser slice; no global mode |
| Parity regression | lower-model sidecar | Header parity, retained trait/impl bodies, no-leak full parse |
| Merge and live measurement | root Codex | One admitted pure-Simple build and one slope run |
| Final review | highest-capability Codex | Parser-state, token-boundary, and parity acceptance |

Frozen helper/API names for this slice are `parse_fn_decl(..., omit_body)`,
`parse_module_body(surface_only)`, `parse_and_build_surface_module`, and
`parse_surface_frontend`. The existing surface interfaces and release marker
remain unchanged.
