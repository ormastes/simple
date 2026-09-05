# Theme package source-capture design hard stop

**Status:** rejected design series; unintegrated
**Series:** `48fbcd1d91`, `ae814abf14`, `7e714f01b0`, `50c886ca9b`
**Iteration state:** three design/review cycles exhausted

## Accepted prerequisite

The canonical immutable codec is landed at
`b1d0b3e27ff8e9c751ee8cbb7ec8f5e41bd4aaeb`:

- module: `src/lib/common/ui/theme_package_wire.spl`;
- wire: `theme-package-install-wire-v1`;
- encoder: `theme_package_install_wire_v1_encode`;
- transaction candidate/publication representation: canonical `text`.

Static review accepted the codec. Its aggregate decoder/encoder ABI probe still
requires an admitted incremental self-hosted runtime before native transaction
consumers may use aggregate values across the module boundary.

## Final design review

The source-capture series correctly specified callback extraction, direct and
module-owned ABI probes, exact-path single reads, captured-byte-only
parsing/composition/hashing, local-only lookup dictionaries, separate
transaction wire caches, and explicit separation from the legacy
`load_theme_package(...) -> ResolvedThemePackage` API.

The final high-capability review still rejected two contradictions:

1. `prepare_theme_package_source_with_reader(...)` requires a constructed
   `ThemePackageSourceReader`, while the warm-hit acceptance test requires that
   no reader be constructed. Construction necessarily happens before entering
   that function. A cache-owning production entry point must check the
   transaction wire caches first, construct the production reader only on a
   miss, then delegate to the injected seam. Alternatively, the requirement
   must be narrowed to “the callback is not invoked.”
2. Strict preparation rejects missing required sources, while the legacy
   compatibility matrix and tests require absent nonblank base/shape/icon/raw
   reference paths to succeed and hash empty content. Both contracts cannot be
   true. Requirements must explicitly select strict transaction rejection or
   legacy missing-core compatibility, then align validation and tests.

No source from the rejected series was integrated. No runtime, bootstrap, seed,
or QEMU command was used.

## Runtime admission state

No source-matched self-hosted runtime currently admits the codec ABI probe.
`67024e9c0a51722812f295cfd7170364f2f031d2` reduced Stage 4 HIR unresolved
names but left receiver and module-key failures, and the generated
`_dispatch_function` still exceeds the practical code-generation/split path.
`a7ac45b72f5d894d416482bf4d2f31e0d7378bbf` restored a missing
`runtime_contracts.c` input but produced no new compiler artifact or provenance
manifest. The retained release binary predates these sources. Therefore neither
the codec aggregate ABI probe nor a hosted theme transaction may be reported as
executed.

## Resume gate

Do not open a fourth source-capture design cycle in this session. A fresh
session may resume only after:

1. defining `prepare_theme_package_source(theme_id) -> Result<text,text>` (or
   an equivalent cache-owning wrapper) that constructs the reader only after a
   cache miss;
2. selecting and documenting the missing-core validation contract;
3. retaining `prepare_theme_package_source_with_reader(...)` as the injected
   miss-path seam;
4. gating native integration on the landed encoder-input ABI probe;
5. keeping the legacy aggregate loader/cache independent until its consumers
   receive a separately reviewed migration.
