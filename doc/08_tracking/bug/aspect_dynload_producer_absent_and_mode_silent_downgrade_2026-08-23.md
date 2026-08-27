# Aspect dynload: producer and loader bridge exist; CLI packaging remains open (2026-08-23)

Status: **PARTIAL** — the producer/writer/reader slice is implemented;
automatic `--mode dynload` packaging and the typed `aspect_facet` language
surface remain **OPEN**. The original audit ran on `origin/main` `c1efb59cf09`
with running evidence, not by reading code. **Nothing was deleted** — the
working half is real and green.

Update 2026-08-24: the smallest producer slice is now implemented in Pure
Simple. `compiler.driver.smf_writer.generate_aspect_pack_smf` delegates to the
canonical linker byte-serialization primitives, which register `.aspect_pack`
as wire type 16, use extension flag `0x40` (leaving `0x20` to note.sdn), and
preserve the SMFAPK1 payload byte-for-byte without widening it through `[i64]`.
The automatic `--mode dynload` input/packaging decision remains OPEN.
`ModuleLoader.load` now performs fail-closed standalone-pack admission and
registers the pack with its lazy lifecycle owner; this does not claim the
broader CLI or typed-facet path.

## 1. What `--mode dynload` is supposed to do vs `--mode one-binary`

`one-binary` emits a single self-contained native artifact. `dynload` is meant
to emit the artifact **plus** the loadable side-channel that lets aspect facets
be acquired lazily at run time. In the pure-Simple driver the only difference is
one line — `src/app/io/_CliCompile/compile_targets.spl:1017`:

```
if build_mode == "dynload" and not emit_object and not emit_archive and not emit_shared:
    options.output_format = driver_output_format_both()   # native + SMF
else:
    options.output_format = driver_output_format_native()
```

The SMF half is where an aspect pack would live, per
`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
§12.1/§23: a `.aspect_pack` SMF section (`SectionType.AspectPackDirectory`, wire
byte 16) carrying an `SMFAPK1` container, which the loader registers with an
aspect-pack loader so a facet routes through the catalog on first use.

Defaults differ per component and this is undocumented: the pure-Simple CLI
defaults to `dynload` (`compile_targets.spl:600`, `native_build_main.spl:103`),
the Rust seed defaults to `one-binary`
(`compiler_rust/driver/src/cli/native_build.rs:49`).

## 2. Which components implement it

| component | dynload |
|---|---|
| `std.common.aspect_pack` (`src/lib/common/aspect_pack.spl`) | **implemented, green** — container, catalog, lazy facet load/unload, signature verification, operational seal |
| Facet registry (`src/compiler/10.frontend/aspect_registry.spl` et al.) | **implemented, green** |
| Loader-side section bridge (`src/compiler/99.loader/aspect_pack_section.spl`) | **IMPLEMENTED** — reads the producer's `.aspect_pack` section |
| SMF writer/driver producer | **IMPLEMENTED** — emits wire type 16, sets extension flag `0x0040`, keeps standalone packs non-executable, and preserves payload bytes directly |
| `ModuleLoader` integration | **IMPLEMENTED** — validates standalone pack geometry before publication, lazily owns one provider, and unregisters it on unload/reload |
| Rust seed | does not implement dynload at all (documented at `native_build.rs:44-49`) |

## 3. Historical running evidence (2026-08-23, before the producer slice)

Measured 2026-08-23, load average 22-38, seed built from `c1efb59cf09`.

Green — aspects genuinely load and dispatch from an in-memory pack:

| spec | verdict |
|---|---|
| `test/01_unit/lib/aspect_pack_spec.spl` | 20/20 pass |
| `test/01_unit/lib/aspect_pack_defect_class_spec.spl` | 25/25 pass |
| `test/01_unit/lib/aspect_pack_acceptance_pending_spec.spl` | 1/1 pass |
| `test/01_unit/lib/facet_registry_spec.spl` | 10/10 pass |

Red — the build-artifact path, **0 of 7**:

```
SPEC FILE VERDICT: test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl
  outcome=ERROR declared>=7 executed=7 passed=0 failed=7
  REQ-APKW-01  semantic: unknown variant or method 'AspectPackDirectory' on enum SectionType
  REQ-APKW-02  semantic: function `smf_build_aspect_pack_image` not found
  REQ-APKW-05  semantic: class `ModuleLoader` has no field named `last_load_aspect_pack_modules`
```

**Historical verdict:** aspects loaded and dispatched, but nothing produced a
pack for them to load from. The producer part of that verdict is superseded by
the 2026-08-24 update. Automatic CLI packaging and typed-facet language routing
remain open; the explicit ModuleLoader-to-pack provider bridge is implemented.

## 4. Defect A — producer absence (closed 2026-08-24)

The original audit found that
`src/compiler/99.loader/aspect_pack_section.spl:5-7` claimed the section was
written by `compiler.backend.linker.smf_writer` when no producer existed. The
Pure Simple writer/driver producer now makes that claim true. This closes only
the production/readback slice, not automatic loader registration or facet
routing.

## 5. Defect B — `--mode dynload` downgrades SILENTLY on the real path

The seed *has* a named skip notice —
`seed_build_mode_notice` (`native_build.rs:61-71`), emitting
`E-SEED-NATIVE-BUILD-MODE-DYNLOAD-UNSUPPORTED`, called at `:473` and unit-tested
at `:740`. **The path a user actually takes never reaches it.** Measured:

```
$ bin/simple native-build --backend=llvm --mode dynload --entry hello.spl -o hello_dyn
rc=0
$ grep -ci dynload build.log     ->  0        # no notice, no warning, nothing
$ cmp hello_simple hello_dyn     ->  identical
```

`bin/simple native-build` delegates to the pure-Simple worker, bypassing
`driver/src/cli/native_build.rs` entirely, so the notice is dead code on this
route. The user asks for dynload, gets a byte-identical one-binary artifact and
**no diagnostic**. That is precisely the "silently half-working" outcome the
notice's own doc comment says the policy forbids.

TODO(dynload-visible-skip): emit a named skip diagnostic from the path
`bin/simple native-build` actually takes (the pure-Simple worker), so
`--mode dynload` cannot succeed silently while producing a one-binary artifact.
Not implemented here: automatic `--mode dynload` packaging and the typed
facet-language surface remain open even though the producer and explicit
ModuleLoader registration bridge now exist (§2).

## 6. Prior art

An unlanded lane exists at `/dev/shm/aspect-loader-operational-seal`
(READ-ONLY, another session's). Its `aspect_acquisition.patch` and
`module_loader.patch` add `loader_aspect_publish_operational` /
`loader_aspect_is_operational` on top of a `src/compiler/99.loader/aspect_acquisition.spl`
that does not exist on main. The library-layer half of that work — the
`apk_loader_seal_operational_state` API — **did** land
(`src/lib/common/aspect_pack.spl:1378`); the loader half did not.
