# Canonical HIR qualification — 2026-11-14

Status: **UNQUALIFIED**. The public canonical availability gate remains false.
No native corpus executable, emitted golden bytes, or runtime PASS exists from
this attempt. Ordinary cold F1 snapshots are a separate capability and do not
qualify canonical equality, warm restoration, or complete-cache authority.

## Gate and admission evidence

`hir_canonical_codec_generated_available_v1` guards canonical encoding and
bounded canonical decoding. Its stated admission conditions are a regenerated
artifact from an admitted self-hosted runtime and independent review of real
HIR golden bytes. Separate portable semantic and live-authority gates remain
independent and closed.

The named-owner schema is HIR v19 / canonical v9, source
`75a60844a9d667003e7e8525e2c8d88f2b547cb8` (equivalent owner patch
`62e239d7e53`). All nine declaration inputs and the three generator sources
match the successful native generator's input worktree byte-for-byte. The
generated codec SHA-256 is
`12f526cdad709b38e1f94d5c21c5e182d939c8f04468684d7cf057db41b51a35`.
Prior generator receipts are reused; successful generation was not rerun.

## Executable fixture

`test/fixtures/hir_canonical_qualification/main.spl` imports actual production
HIR records, generated encoder/decoder, reader, writer, and header helper.
It uses no replacement codec, reduced records, or hand-emitted golden bytes.
Its authored checks cover signed i64 and SymbolId ordering, unsigned UTF-8
ordering, dictionary insertion permutations, source immutability, real constant
and named-advice round trips, integer three, escaped text, truncation, duplicate
keys, decoder budgets, writer budgets/depth, exact framed byte limits, and an
unsupported opaque HIR payload. Trailing and permuted records are explicitly
tested as detectable by admission, not falsely described as raw decoder
refusals. All checks remain unrun.

Astra reviewed the source boundary and requested stronger finish, ordering,
depth, and exact-budget oracles; those corrections are included. This source
review is not independent golden review.

## Bounded native attempt 1

- Frozen source: `9f273517679add1dbdbb3fdf8cee7282bd3682c0`.
- Producer: admitted **phase 2**, SHA-256
  `855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
- Source includes `808b71bc91b`, the landed RuntimeValue arity fix.
- Provider: `core-c`; one requested compiler thread; real source imports.
- Sources: `src` and `test/fixtures/hir_canonical_qualification`; entry is
  `test/fixtures/hir_canonical_qualification/main.spl`; `--entry-closure`.
- Repository process-tree RSS watchdog: 4,194,304 KiB, 300 seconds.
  No address-space cap or forged worker estimate was used.
- Actual closure: 457 modules, 721 source files. HIR completed 6/457 modules;
  the active module was `compiler.hir.generated.hir_codec`.
- Outcome: exit **88**, `rss-cap-exceeded`, peak **4,245,568 KiB**.
  No executable was produced. No retry was performed.

Evidence and reusable cache are retained at
`/tmp/hir-canonical-qualification-evidence-20261114`: `inputs.sdn`,
`compile1.log`, `compile1.rss.env`, and `cache/`. The frozen worktree is
`/tmp/simple-hir-canonical-qualification-20261114`.

## Remaining admission work

Execute the actual imported codec under an admitted resource/runtime path;
retain real raw and framed golden artifacts plus source/runtime hashes;
independently inspect their bytes; qualify public canonical encode/bounded
decode exact-consumption and refusal behavior. Parser-produced corpus,
decoded-HIR downstream execution, warm F1 restoration, and complete-cache
authority require their own evidence. An extracted diagnostic projection, if
later used, must remain explicitly provisional and cannot substitute for these
unmet checks.
