<!-- codex-design -->
# Shared Multilingual GPU Fonts System Test Plan

## Scope

Three draft SSpec files cover manifest/assets, shared 2D/3D batch, and portable
emission. A fourth native graphics readback scenario remains planned and does
not exist yet. Unit/integration suites for the
existing shaper, Engine2D, Engine3D texture path, emitter, and backend readback
remain supporting evidence; they do not replace these end-to-end scenarios.

Planned executable/manual pairs:

| Executable SSpec | Generated manual |
|---|---|
| `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_manifest_spec.md` |
| `test/03_system/app/simple_2d/feature/shared_font_surfaces_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/shared_font_surfaces_spec.md` |
| `test/03_system/app/simple_2d/feature/gpu_font_emission_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/gpu_font_emission_spec.md` |
| `test/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.spl` | `doc/06_spec/03_system/app/simple_2d/feature/native_gpu_font_readback_spec.md` |

Excluded claims: multicolor/CFF/non-default variations, GPU shaping/outline
rasterization, and native success on unavailable hardware.

## Frozen scenario vocabulary

Visible primary steps:

- `step("Load the pinned multilingual font manifest")`
- `step("Prepare one shared font batch for 2D and 3D")`
- `step("Emit the selected font composite program and plan compilation")`
- `step("Prove native submission and device readback")`

Shared helpers are `setup_shared_font_fixture`, `expect_font_license`,
`expect_language_coverage`, `expect_shared_font_batch`,
`expect_backend_emission`, and `expect_font_render_parity`. Until implemented,
each helper fails explicitly. New assertions use built-in matchers only.

## Requirement traceability

Each listed case count is a minimum and includes happy, boundary, and failure
behavior.

| Requirement | Spec | Required cases | Current/required |
|---|---|---|---:|
| REQ-001 | `shared_font_manifest_spec.spl` | pinned hashes/top ten; script totals; tenth/eleventh boundary | 3 |
| REQ-002 | `shared_font_manifest_spec.spl` | fixed decimal/fallback; alias/macrolanguage policy; double regeneration | 3 |
| REQ-003 | `shared_font_manifest_spec.spl` | complete sparse cells; honest fallback; unavailable/not-designed distinction | 3 |
| REQ-004 | `shared_font_manifest_spec.spl` | complete license metadata; checksum/table validation; missing field rejection | 3 |
| REQ-005 | `shared_font_manifest_spec.spl` | pinned catalog revision; unchanged accepted bytes; corpus rejection | 3 |
| REQ-006 | `shared_font_surfaces_spec.spl` | one owner; identical batch identity; no duplicate material cache | 3 |
| REQ-007 | pending shaping acceptance spec | selected-script shaping; BiDi/cluster offsets; missing-glyph fallback | 0/3 |
| REQ-008 | `shared_font_manifest_spec.spl` | compound/default-glyf corpus reconstruction; unsupported-format/axis rejection and bitmap fixture pending | 1/3 |
| REQ-009 | `shared_font_surfaces_spec.spl` | key separation; bounded eviction/counters; generation/dirty regions | 3 |
| REQ-010 | `gpu_font_emission_spec.spl` | five source targets; Vulkan contract; deterministic failures/hashes | 3 |
| REQ-011 | `shared_font_surfaces_spec.spl` | Engine2D API compatibility; DrawIR/batch evidence; CPU parity | 3 |
| REQ-012 | pending native-readback spec | HUD transform; world depth/transform; texture-to-readback chain | 0/3 |
| REQ-013 | pending native-readback spec | promoted backend pass; unavailable classification; fake proof rejection | 0/3 |
| REQ-014 | three present specs plus pending native-readback spec | zero-stub manuals; guide/notice freshness; evidence-recipe audit | 2/3 |

| NFR | Evidence | Pass condition |
|---|---|---|
| NFR-001 | manifest spec and regeneration hashes | all immutable and byte-identical; corruption fails closed |
| NFR-002 | native readback comparator fixture | exact integer-alpha RGBA8; bounded documented AA edges |
| NFR-003 | manifest asset-size total | core fonts plus notices `<= 80 MiB` |
| NFR-004 | surfaces benchmark | warm hits `>=95%`; p95 `<=4 ms` 1080p and `<=8 ms` 4K |
| NFR-005 | native equal-semantics benchmark | 4,096 glyph end-to-end p95 `>=1.25x` CPU |
| NFR-006 | upload/resource/RSS counters | no unchanged full upload; RSS `<=10%`; GPU `<=128 MiB` |
| NFR-007 | corrupt/device-loss scenarios | stable active identity and unchanged CPU-fixture p95 |
| NFR-008 | native evidence record | every required stage/handle/hash/fence/readback field is present |

## Oracles and evidence

- Manifest oracle: source hashes, expected manifest hash, exact ordered IDs,
  full contribution recomputation, and cutoff evidence.
- Surface oracle: shaped glyph/cluster records and identical batch/atlas identity
  before structured 2D/3D object evidence.
- Emission oracle: target-specific entry/syntax markers, exported symbol,
  version/source hash, and compile plan. It makes no execution claim.
- Native oracle: nonzero resource handles, submitted batch hash, completed fence,
  device-origin marker, nonblank absolute glyph pixels, and CPU comparison.
- Raster captures are `artifact` evidence linked from manuals; structured batch,
  DrawIR, and native evidence records appear first. Hardware-unavailable rows are
  recorded as `unavailable`, never passed by simulation.

## Environment and order

Use the self-hosted release binary. Run manifest first, then shared surfaces,
emission, and native readback. Native specs require a declared promoted graphics
backend/driver; other backends may provide compile-only rows. Pin fixtures,
viewport, premultiplication, rounding, warmups, samples, and percentile method.

For each changed spec, run native execution and generate its manual once:

```text
bin/simple test <spec> --native
bin/simple spipe-docgen <spec> --output doc/06_spec --no-index
```

Then run the existing UI SSpec evidence audit and require
`find doc/06_spec -name '*_spec.spl'` to return no paths.

## Manual rendering policy

Primary frozen steps stay visible. Fixture construction and reusable checks are
`@inline`/`@prev`; matrix, corruption, stress, and performance detail is folded.
Executable SSpec is folded by default. Each generated manual must read as an
operator flow without opening source and docgen must report zero stubs.

## Pass/fail

Pass requires every REQ/NFR row above, four zero-stub manuals, one real promoted
graphics backend for both 2D and 3D, and all selected thresholds. Missing
hardware is not a failure for non-promoted rows, but no promoted native row is a
release failure. Placeholder assertions, environment-only payloads, mirrors, or
upload-only evidence fail.
