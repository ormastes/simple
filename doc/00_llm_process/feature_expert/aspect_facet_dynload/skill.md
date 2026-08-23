# Feature Expert: Aspect Facet Dynload

## What this is
Lazy, run-time acquisition of AOP **aspect facets** from a pack carried inside a
built artifact, rather than weaving every aspect in at compile time. The build
knob is `--mode dynload` on `native-build`; the wire format is an `SMFAPK1`
container in an SMF `.aspect_pack` section.

**Do not confuse this with `spl_dlopen`.** `src/runtime/runtime_dynload.c`
(`spl_dlopen`/`spl_dlsym`/`spl_dlclose`) is the general hosted FFI facility used
by `std.nogc_sync_mut.ffi.dynamic` and font loading. Aspect dynload does **not**
go through it — facets come out of an SMF section, not a shared object. The
similarity of names has already misled one investigation.

## Status (audited 2026-08-23, origin/main c1efb59cf09 — with running evidence)

| half | state |
|---|---|
| Pack library + catalog + lazy load/unload + signature + operational seal | **works**, 46/46 examples green |
| Facet registry | **works**, 10/10 green |
| Loader-side SMF section bridge | code exists, **no producer to read from** |
| SMF **writer** side | **does not exist** |
| `ModuleLoader` registration hop | **does not exist** |
| Rust seed | never implemented dynload; documented at `native_build.rs:44-49` |

`test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl` is
**0/7 RED and correctly so**. It is the specification of the missing producer.
**Never green it by weakening it, and never delete the reader half.**

Two live defects, both filed:
`doc/08_tracking/bug/aspect_dynload_producer_absent_and_mode_silent_downgrade_2026-08-23.md`
1. no producer (above);
2. `--mode dynload` on `bin/simple native-build` emits a **byte-identical**
   one-binary artifact with **no diagnostic** — the seed's
   `E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED` notice exists and is
   unit-tested but sits on a code path the real invocation never reaches.

## Source of truth
- Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` §12.1, §23.

## Code map
| File | Role |
|---|---|
| `src/lib/common/aspect_pack.spl` | `SMFAPK1` container, `apk_loader_*`, `apk_load_facet`, `apk_loader_seal_operational_state` |
| `src/compiler/99.loader/aspect_pack_section.spl` | reader: SMF section -> `apk_loader_register_pack`. Header comment corrected 2026-08-23 (it used to claim a writer that does not exist) |
| `src/compiler/99.loader/aspect_pack_index_cache.spl` | pack index cache |
| `src/compiler/10.frontend/aspect_registry.spl` | facet registry |
| `src/compiler/35.semantics/forbidden_io_checker.spl` | denies `apk_load_facet` from forbidden contexts (ISR etc.) |
| `src/app/io/_CliCompile/compile_targets.spl:600,1017` | the ONLY behavioural effect of `--mode dynload` today: `output_format = both` (native + SMF) |
| `src/compiler_rust/driver/src/cli/native_build.rs:49,61-71,473` | seed default `one-binary`; the unreached skip notice |

## Gotchas
- Defaults **differ by component and this is easy to get wrong**: pure-Simple CLI
  defaults `dynload`; the Rust seed defaults `one-binary`.
- Prior art at `/dev/shm/aspect-loader-operational-seal` is another session's
  worktree — READ ONLY. Its library half landed; its `aspect_acquisition.spl` /
  `loader_aspect_*` half did not (`grep -rn loader_aspect_ src/` = 0 hits).
