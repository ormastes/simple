# Shared Multilingual Font Manifest Specification

> **Hand-maintained mirror — pending canonical `spipe-docgen`.** The executable
> SSpec changed after the recorded run; this file does not claim current PASS.

Status: **PENDING post-change execution and docgen**.

Executed command:

```text
bin/release/simple test test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl --mode=interpreter
```

That recorded run predates the current asset hashes and coverage counts. The
post-change self-hosted rerun timed out without output, so no current scenario
PASS is inferred.

Executable source:
`test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl`

## Scope

This scenario checks the repository-owned pinned CLDR bytes and hashes,
independent contribution arithmetic, byte-identical double regeneration, the
selected top-ten/rank-eleven boundary, 16 unchanged font assets with adjacent
metadata/licenses, all 100 sparse language/category cells, and a fail-closed
rasterizer witness gate. It does not claim that all 16 candidates have passed
corpus acceptance, or claim GPU/native execution.

The source covers REQ-001/REQ-002 source hashes,
contribution replay, deterministic ranking, script subtotals, and cutoff;
remaining coverage is REQ-003, static/hash portions of REQ-004/005 and NFR-001,
plus the NFR-003 font-byte limit. It does not prove complete REQ-007
complex shaping, complete REQ-008 format behavior, or GPU execution.

## Operator flow

### Load the pinned multilingual font manifest

1. Run the executable SSpec with the self-hosted pure-Simple runtime.
2. Observe the visible step: **Load the pinned multilingual font manifest**.
3. Confirm the scenario completes without skipped or pending examples.
4. Retain the exit status and output as the evidence record; this mirror alone
   is not executable evidence.

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
  copyright text, RFN state, and script metadata. The manifest also pins
  extracted style, full/PostScript names, version, default axes, and a closed
  fallback role.
- Every binary replays its pinned family, subfamily, full, PostScript, and
  version identity directly from the sfnt `name` table; Noto Emoji's embedded
  full name is `Noto Emoji Regular`.
- Every candidate references the same immutable multilingual witness corpus;
  `CORPUS.sdn` is recomputed as
  `sha256:c7cffbf3e1a29c75dcd481593c6880d071966c5cbf0611e2185fe0d73e0c83f6`.
- Allowed licenses are `OFL-1.1` and `Apache-2.0`.
- Roboto Slab's separate `apache/robotoslab/COPYRIGHT.txt` exists, is nonempty,
  and names the 2018 Roboto Slab Project Authors.
- Exact binary total: `51,764,704` bytes. The distribution gate separately
  sums every unique binary, `METADATA.pb`, license, and copyright notice and
  requires the complete package to remain below 80 MiB.

### Sparse coverage

- 10 languages × 10 categories = exactly 100 unique cells.
- Current source-policy totals are 67 `native`, 4 `fallback`, 26
  `not-designed-for-script`, and 3 `unavailable`.
- Chinese mono falls back to Noto Sans SC; Hindi, Arabic, and Urdu mono fall
  back to their accepted script sans faces. Hindi, Arabic, and Urdu serif remain
  unavailable pending executable proof of their existing exact per-face
  oracles. Exact monochrome Noto Emoji
  `U+1F600` corpus tuples are native for all ten selected language tags;
  sequences and color remain unsupported.
  Russian display remains not designed for that script.

### Corpus and accepted-simple policy gate

- Twelve manifest entries are accepted: nine identity-profile families plus the
  sans Devanagari/Arabic selected-shaping faces and exact-corpus Noto Emoji. The
  two serif script faces and two Bengali rank-eleven faces remain `candidate:`. Cmap
  metadata or raster diagnostics alone still cannot accept a cell; the shaping
  gate adds exact Hindi `hi` through the `हिन्दी` `dev2` witness for Noto Sans
  Devanagari and the exact pinned Arabic `العربية` / Urdu `اردو` lookup-vector
  witnesses for Noto Sans Arabic.
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
  structural bool preflight before native state mutation; typed reasons are
  retained as scenario evidence.
- The bound shaping gate promotes 54 identity native cells, three selected-script
  sans cells, and ten exact-corpus Emoji cells, for 67 `native`, 4 explicit
  script-sans mono `fallback` cells, 26 `not-designed-for-script`, and 3
  `unavailable`. This manifest validates that
  source policy but adds no shaping rows beyond the shaping gate.
- The focused shaping SSpec preserves exact CORPUS
  source/cluster/language/script metadata for the 54-cell identity subset and
  separately checks exact Hindi `हिन्दी` and Arabic/Urdu witnesses through the
  accepted sans faces, plus exact single-`U+1F600` material; other complex and emoji
  sequences remain incomplete. This manifest does not extend that evidence or
  substitute for the shaping spec's current run.
- A test-only raw sfnt oracle independently identifies 14 compound-bearing
  faces and the exact 76 compound corpus roots/124 direct components. Every
  mapped root must produce a nonempty Pure Simple outline; this adds no native
  production owner and does not promote the matrix.
- Focused supporting specs now reject color/CFF/SVG/current and legacy bitmap
  strike tables, accept only static or exact default-axis requests, repeat the
  pinned Pixelify Sans `wght=400` Pure Simple raster, and pin the built-in 8×16
  monochrome fallback glyph. No admitted pure-Simple runner currently executes
  these refreshed specs, so this manual does not upgrade REQ-008 to runtime PASS
  or claim non-default `gvar` interpolation.

### Global-face wrapper invalidation

- The conditional native scenario loads selected face A, then selected face B
  through the same available rasterizer dylib without closing A first.
- B must remain current and expose exactly
  `sha256=<manifest digest>;axes=<manifest defaults>`. A must become stale,
  expose an empty cache identity, reject glyph lookup, alpha/subpixel material,
  layout, kerning, and line metrics, and never read B through A's wrapper.
- Closing stale A must not invalidate B; B must still find and rasterize `A`
  before it is closed.
- If no candidate rasterizer dylib exists, the scenario fails explicitly as
  `unavailable`; missing native evidence is not a synthetic PASS.

The expanded scenario source is current, but its post-change execution and
canonical doc generation are pending after the recorded timeouts.

<details>
<summary>Folded executable detail</summary>

The SSpec calls the canonical registry helpers, hashes real files through
`package_sha256`, reads notices through the owned file facade, sums immutable
byte lengths, rejects duplicate paths/hashes, and validates every matrix key
and status with built-in matchers. Consult the executable source for exact
assertions; no copied source block is maintained here.

</details>

## Claim boundary

The source specifies manifest and embedded-name identity, current sparse
policy, and codepoint/raster evidence. Pending execution means it does not yet
establish a current PASS, and it does not independently prove the
accepted-simple shaping rows, complete complex shaping, GPU compilation,
submission, readback, or display.
