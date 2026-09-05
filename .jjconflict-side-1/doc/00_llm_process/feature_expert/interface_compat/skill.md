# Feature Expert: Interface Compatibility & SMF Artifact Metadata

## What this is
The four-digest identity model that decides whether a dependent module must be
recompiled, plus the SMF metadata section those digests will eventually travel in.

**Core rule:** an ordinary dependent is recompiled only when the new provider no
longer satisfies the compile-time interface requirements recorded when that
dependent was compiled. Implementation changes alone must not propagate.

```
ImplementationDigest    body / private implementation changed
CompileInterfaceDigest  caller-visible type-check + name-resolution assumptions
AbiInterfaceDigest      already-generated machine code can no longer call safely
CompileSemanticDigest   macros, CTFE constants, AOP selection, inlining contracts
```

**Status: compute-and-log only. Wired into NO build decision.**

## Source of truth
- Plan: `doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md`
  §7 (canonical signatures), §9 (compatibility policy), §13 (SMF metadata), §20 (first slice).
- Normative artifact schema: `src/spec/artifact/smf_v1_2.sdn`
- Known gaps: `doc/08_tracking/bug/cache_v2_first_milestone_known_gaps_2026-08-10.md`
- **SMF divergence defect:** `doc/08_tracking/bug/smf_header_wire_layout_diverges_rust_vs_simple_2026-08-10.md`
- Blocked work: `doc/08_tracking/bug/a2_target_ir_blocked_on_untracked_target_graph_2026-08-10.md`

## Code map
| File | Role |
|---|---|
| `src/compiler/35.semantics/interface/compile_interface.spl` | `CompileInterfaceDigest` over the public API surface, sorted-set canonical encoding via `action_key.spl`'s `canon_*` helpers. Excludes comments, formatting, line numbers, private decls, bodies, paths. |
| `src/compiler/35.semantics/interface/module_identity.spl` | `ModuleIdentity`; `compute_module_identity(surface, source)`. |
| `src/spec/artifact/smf_v1_2.sdn` | Normative SMF layout + the v1.2 `.simple_meta` TLV design. |
| `src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl` | Pins the Simple layout AND the known Rust divergence, so an accidental one-sided "fix" is caught. |

Specs: `test/01_unit/compiler/interface_compat/compile_interface_spec.spl` (7).

## Landmines

- **THE SMF HEADER IS NOT WIRE-IDENTICAL ACROSS IMPLEMENTATIONS.** Rust seed = 96 B
  with `#[repr(C)]` alignment padding; Simple = 128 B packed. `section_table_offset`
  is at **24** in Rust, **20** in Simple — every later field shifts by 4. Trailers
  are at EOF−96 vs EOF−128, so each side's magic check fails on the other's file and
  falls back to a v1.0 offset-0 **misparse rather than a clean error**. Rust also
  raw-`memcpy`-casts the struct, so its "format" is really the host ABI.
  Do NOT change either layout unilaterally — both sides have artifacts on disk.
  Fix path is the dual-write migration in plan §13.5.
- **Allocate no new fixed-header byte.** New metadata goes in the `.simple_meta` TLV
  section precisely so the header never has to move again. Wanting a new header
  field is the failure mode this design exists to prevent.
- **`ApiSurface` lacks generic arity/constraints, effects, and param passing modes.**
  The frozen spec requires them in `CompileInterfaceDigest`; they are absent. A
  change to a generic bound or a declared effect may therefore NOT change the digest
  — an **under-invalidation** risk, and the reason this stays compute-and-log.
- **Unknown visibility defaults to public** in the digest. That is the safe
  direction: it over-includes (extra invalidation) rather than under-invalidates.
- `abi_interface_digest` / `compile_semantic_digest` / `link_export_digest` are
  placeholder-domain re-hashes of the compile part set. They must NOT drive a reuse
  decision. Only `compile_interface_digest` and `implementation_digest` mean anything.
- `normalize_module_source` strips `#` comments without string-literal awareness, so
  a `#` inside a text literal is mis-stripped. Affects `implementation_digest` only.
- **Reuse `action_key.spl`'s encoder. Never introduce a second hash scheme.**

## Verification
```bash
bin/simple test test/01_unit/compiler/interface_compat/compile_interface_spec.spl  # 7/7
bin/simple test src/compiler/70.backend/linker/test/smf_layout_parity_spec.spl     # 7/7
```
Required acceptance properties: body-only change → same compile digest, different
implementation digest; comment/format-only → same; private decl added → same;
public signature change → different; declaration iteration order → identical digest.

Sabotage-probe the "public signature change → different digest" case. If it cannot
fail, the digest is not reading the signature at all.
