# Feature Expert: Generic instance traceability through TLDR

## What this is
Full monomorphization as an async, on-demand query: a generic instance is a
compile task keyed by `ConcreteTldrKey`, and every request is a TLDR fact.
Stages S3-F0..F10 of `doc/03_plan/language/type_system/no_any_inference_plan.md`.
Landed so far: the data contracts of the early-start set (S3-F1 provider,
S3-F2 consumer). **No instance is requested, built or linked yet**: the async
engine steps that gate S3-F3 onward are not in `src`.

## Source of truth
- Design: `doc/05_design/compiler/cache/generic_instance_tldr_trace.md` (TLDR beside it)
- Plan: `doc/03_plan/language/type_system/no_any_inference_plan.md` (S3-F rows, critical path table)

## Code map
| File | Role |
|---|---|
| `src/compiler/00.common/cache_contract/generic_open_need_v1.spl` | Leaf. `GenericOpenNeedV1` row, canonical order, identity digest (no span, no cause), `GenericOpenNeedsSlotV1` (`Absent` / `Filled`), byte-framed nested frame codec shared by both sections |
| `src/compiler/00.common/cache_contract/generic_template_section_v3.spl` | S3-F1. `generic-template-section/v3` = sealed v2 section as one frame + one open-needs slot per entry; set-once `generic_template_fill_open_needs_v1` |
| `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl` | Entry struct; `open_needs` is its trailing field (no logic added there) |
| `src/compiler/00.common/cache_contract/needed_instance_v1.spl` | S3-F2. `needed-instance|` section: rows by `ConcreteTldrKey` with merged origins, `Complete` / `Incomplete`, producer from concrete views, sealed codec |
| `src/compiler/30.types/generic_subst/generic_concrete_view_v1.spl` | S3-F2. `acquire_concrete_tldr_v1` (Concrete / Partial / Unresolved) and `generic_resolved_needs_v1`; the only importer of `generic_subst_model` on this path |

Specs: `test/01_unit/compiler/cache/{generic_open_need_v1,generic_template_section_v3,needed_instance_v1}_spec.spl`,
`test/01_unit/compiler/30.types/generic_subst/generic_concrete_view_v1_spec.spl`.

## Rules that are easy to break
- `open_needs` is in NO template fingerprint and not in the v1/v2 wire form.
  v3 bumps the section magic only; `language_schema` stays v2, so no
  TemplateId or `ConcreteTldrKey` moves.
- Two digests everywhere: the identity / invalidation digest excludes spans,
  causes and requesting modules; the section seal covers them.
- Only a `Concrete` view becomes a `needed-instance|` row. Partial and
  Unresolved mark the set `Incomplete`; an incomplete set is not a cache hit
  and never falls back to an erased body in safe code.
- An `any` argument is admitted only from an unsafe or script origin.
- One substitution implementation: `generic_subst_model` (S3-F0). Do not add a
  key parser or a substituter to `00.common`.
- Decoders are strict inverses: the bytes must equal what the encoder writes.

## Landmines
- `text.len()` counts characters; `byte_len` / `byte_at` / `substring` are the
  byte family. The frame codec is byte-framed throughout.
- Type keys are byte-framed on both sides (v2 projector, `generic_subst_model`
  from S3-F0 `8eed05d228f` on); the v1 projector frames by characters.
- `generic_tldr_view_v1.spl` is far below the 95 % decision/condition gate and
  its MC/DC spec is red on the seed (S3-F10 owns that). Keep new logic out of it.
- New pub API must not add bare primitives (`check-primitive-api-added.shs`):
  use enums (`NeededInstanceCompletenessV1`), newtypes (`GenericSourceOffsetV1`)
  and `Result`.

## Not wired yet
- No typed-HIR producer fills `open_needs` or writes `needed-instance|`
  (needs plan S2-C write-back); `module_artifacts_v1.spl` still writes the v1
  template section.
- Per-instance key record (S3-F5), request / slot table (S3-F3), reverse
  reference rows (S3-F6), coverage gate script (S3-F10).
