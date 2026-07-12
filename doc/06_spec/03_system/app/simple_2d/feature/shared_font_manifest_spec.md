# Shared Multilingual Font Manifest Specification

> **Manual draft — pending canonical `spipe-docgen`.** This document mirrors
> the current executable SSpec for review while the pure-Simple compiler build
> is in progress. It is not generated-run evidence and does not claim a PASS.

Executable source:
`test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl`

## Scope

This scenario checks the repository-owned pinned CLDR bytes and hashes,
independent contribution arithmetic, byte-identical double regeneration, the
selected top-ten/rank-eleven boundary, 16 unchanged font assets with adjacent
metadata/licenses, all 100 sparse language/category cells, and a fail-closed
rasterizer witness gate. It does not claim that all 16 candidates have passed
corpus acceptance, or claim GPU/native execution.

When executed, the CLDR portion covers REQ-001/REQ-002 source hashes,
contribution replay, deterministic ranking, script subtotals, and cutoff;
remaining coverage is REQ-003, static/hash portions of REQ-004/005 and NFR-001,
plus the NFR-003 font-byte limit. This unexecuted draft is not PASS evidence and
does not prove complete candidate acceptance, REQ-007 shaping, or REQ-008
format behavior.

## Operator flow

### Load the pinned multilingual font manifest

1. Run the executable SSpec with the self-hosted pure-Simple runtime once it is
   available.
2. Observe the visible step: **Load the pinned multilingual font manifest**.
3. Confirm the scenario completes without skipped or pending examples.
4. Retain the executable test output as the evidence record; this draft alone
   is not evidence.

## Expected evidence

### CLDR ranking and cutoff

- Release: `release-48-2`
- Annotated tag object: `fc1fd058cc6f50544a450a3b15a4bba0e0c1e653`
- Source commit: `11299982335beb974c1c63c45265184e759c0f41`
- License: `Unicode-3.0`
- The three pinned source-document SHA-256 values are recomputed from bundled
  CLDR bytes and match exactly; license, tag witness, source manifest, and
  derived ranking ledger hashes are also exact.
- Two real-input generations are byte-identical to `RANKING.sdn`, and all
  eleven language totals plus script subtotals match the registry.
- All 1,589 territory/language contributions are independently recomputed from
  their fixed-decimal source fields with the specified half-up rule.
- Selected order: `en, zh, es, hi, ar, fr, pt, ru, ur, id`.
- Boundary row: `bn` is eleventh; Indonesian total `167542007` is greater
  than Bengali total `167485664`.

### Bundled assets and notices

- Exactly 16 unique font paths and 16 unique SHA-256 values.
- Every binary, adjacent `METADATA.pb`, and adjacent license file exists below
  `assets/fonts/google-fonts/`, and the metadata/license text is nonempty.
- Every binary's SHA-256 is recomputed through the package facade and equals
  `sha256:` plus its pinned manifest digest.
- Every font is unchanged, records `cmap` and `glyf`, and has nonempty
  copyright text plus an RFN state. The manifest also pins extracted style,
  full/PostScript names, version, default axes, and a closed fallback role.
- Every binary replays its pinned family, subfamily, full, PostScript, and
  version identity directly from the sfnt `name` table; Noto Emoji's embedded
  full name is `Noto Emoji Regular`.
- Every candidate references the same immutable multilingual witness corpus;
  `CORPUS.sdn` is recomputed as
  `sha256:c7cffbf3e1a29c75dcd481593c6880d071966c5cbf0611e2185fe0d73e0c83f6`.
- Allowed licenses are `OFL-1.1` and `Apache-2.0`.
- Roboto Slab's separate `apache/robotoslab/COPYRIGHT.txt` exists, is nonempty,
  and names the 2018 Roboto Slab Project Authors.
- Exact binary total: `51,764,704` bytes, below the selected 80 MiB ceiling.

### Sparse coverage

- 10 languages × 10 categories = exactly 100 unique cells.
- Until the exact shaping corpus passes, status totals are 0 `native`, 0
  `fallback`, 26 `not-designed-for-script`, and 74 `unavailable`.
- Representative checks keep Chinese sans, Hindi mono, Urdu serif, and emoji
  unavailable while their candidates are provisional; Russian display remains
  not designed for that script.

### Provisional corpus gate

- All 16 manifest entries remain explicitly `candidate:` with executable Simple
  shaping acceptance pending; none may report `accepted` from cmap metadata or
  raster diagnostics.
- The existing `FontRasterizer` facade loads every pinned face and exercises its
  exact applicable `CORPUS.sdn` codepoints across Latin, Han, Devanagari,
  Arabic, Urdu, Cyrillic, Bengali rank 11, and Common `U+1F600` emoji.
- Every witness codepoint must exist and rasterize, and each whole witness must
  produce a nonempty diagnostic layout. That layout is not shaping acceptance.
  A missing rasterizer library is a failure, not a synthetic pass.
- Before those diagnostics, the scenario reads each binary once and checks the
  shared typed sfnt validator, the complete recorded table set, and the exact
  static/default-variable axis metadata. It also replays the five pinned sfnt
  names from each real binary. Both native loader owners call the
  structural bool preflight before native state mutation; typed reasons remain
  scenario evidence and this scenario still needs execution.
- The matrix remains 0 `native`, 0 `fallback`, 26
  `not-designed-for-script`, and 74 `unavailable`; no cell may be promoted until
  the bound Pure Simple shaping gate runs successfully.
- Focused shaper fixtures now preserve exact CORPUS source/cluster/language/
  script metadata and reject complex-script material while GSUB/GPOS remain
  incomplete. These fixtures were not executed in this session and do not
  promote a candidate.

The expanded scenario was not run in this session because the mandatory
three-attempt Simple command cap was already exhausted.

<details>
<summary>Folded executable detail</summary>

The SSpec calls the canonical registry helpers, hashes real files through
`package_sha256`, reads notices through the owned file facade, sums immutable
byte lengths, rejects duplicate paths/hashes, and validates every matrix key
and status with built-in matchers. Consult the executable source for exact
assertions; no copied source block is maintained here.

</details>

## Claim boundary

This manual establishes manifest and embedded-name identity plus
codepoint/raster evidence only after
its SSpec runs. It does not accept any candidate or prove Pure Simple
shaping, GPU compilation, submission, readback, or display.
