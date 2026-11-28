# Feature Expert: Generic instance traceability through TLDR

## What this is
Full monomorphization as an async, on-demand query: a generic instance is a
compile task keyed by `ConcreteTldrKey`, and every request is a TLDR fact.
Stages S3-F0..F10 of `doc/03_plan/language/type_system/no_any_inference_plan.md`.
Landed so far: the provider data contract (S3-F1). **No instance is requested,
built or linked yet**: the async engine steps that gate S3-F3 onward are not in
`src`.

## Source of truth
- Design: `doc/05_design/compiler/cache/generic_instance_tldr_trace.md` (TLDR beside it)
- Plan: `doc/03_plan/language/type_system/no_any_inference_plan.md` (S3-F rows, critical path table)

## Code map
| File | Role |
|---|---|
| `src/compiler/00.common/cache_contract/generic_open_need_v1.spl` | Leaf. `GenericOpenNeedV1` row, canonical order, identity digest (no span, no cause), `GenericOpenNeedsSlotV1` (`Absent` / `Filled`), byte-framed nested frame codec |
| `src/compiler/00.common/cache_contract/generic_template_section_v3.spl` | S3-F1. `generic-template-section/v3` = sealed v2 section as one frame + one open-needs slot per entry; set-once `generic_template_fill_open_needs_v1`; `GenericTemplateSectionV3` carries the v3 seal |
| `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl` | Entry struct; `open_needs` is its trailing field (no logic added there) |

Specs: `test/01_unit/compiler/cache/{generic_open_need_v1,generic_template_section_v3}_spec.spl`.

## Rules that are easy to break
- `open_needs` is in NO template fingerprint and not in the v1/v2 wire form.
  v3 bumps the section magic only; `language_schema` stays v2, so no
  TemplateId or `ConcreteTldrKey` moves.
- Two digests everywhere: the identity digest excludes spans and causes; the
  section seal covers them. For a v3 section, `section.digest` is the v2 table
  digest (templates only) and `seal` also covers the open needs.
- Canonical order is the bytewise order of UTF-8 text and is part of every
  sealed section. Only the seed interpreter is verified; the native text `<`
  must agree before a native build reads or writes these sections.
- Decoders are strict inverses: the bytes must equal what the encoder writes.
  Whatever the encoder accepts the decoder must accept (span offsets are capped
  at twelve digits, sections at 16 MiB, on both sides).
- Do not add a type-key parser or a substituter to `00.common`: the one
  substitution implementation is `generic_subst_model` (S3-F0).

## Landmines
- `text.len()` counts characters; `byte_len` / `byte_at` / `substring` are the
  byte family. The frame codec is byte-framed throughout.
- `generic_tldr_view_v1.spl` is far below the 95 % decision/condition gate and
  its MC/DC spec is red on the seed (S3-F10 owns that). Keep new logic out of it.
- New pub API must not add bare primitives (`check-primitive-api-added.shs`):
  use enums, newtypes (`GenericSourceOffsetV1`) and `Result`.

## Not landed yet
- S3-F2 (the `needed-instance|` companion section and concrete-view
  acquisition) is written and waits for S3-F0. Its review decided three schema
  changes that land with it: an admission marker (safe / unsafe / script) on
  need rows, acquisition as the only constructor of Concrete views, and
  template module + symbol on needed-instance rows for request replay.
  The marker changes the open-need row wire form of this stage.
- No typed-HIR producer fills `open_needs` (needs plan S2-C write-back);
  `module_artifacts_v1.spl` still writes the v1 template section.
- Per-instance key record (S3-F5), request / slot table (S3-F3), reverse
  reference rows (S3-F6), coverage gate script (S3-F10).
