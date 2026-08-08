# Production GUI/web renderer parity evidence

> Validates the production parity wrapper contract without launching the real
> renderer stack.

| Tests | Active | Skipped | Pending | Stubs |
|-------|--------|---------|---------|-------|
| 22 | 22 | 0 | 0 | 0 |

| Field | Value |
|-------|-------|
| Source | `test/03_system/check/production_gui_web_renderer_parity_evidence_spec.spl` |
| Plan | `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` |
| Guide | `doc/07_guide/tooling/renderdoc_capture_infra.md` |

## Trust boundary

The top-level wrapper requires an explicit current-source Stage4 binary and its
adjacent `${SIMPLE_BIN}.provenance.env`. It calls the canonical Stage4
provenance verifier directly, performs no release/Stage3/repository/`PATH`
discovery, and exits nonzero before nested checks when admission fails.

## Visible helpers

- `make_stage4_receipt_fixture(root, stale)` creates the executable and
  receipt-shaped negative fixtures used by the admission scenarios.
- `run_renderer_evidence_wrapper(wrapper, root)` invokes the selected evidence
  wrapper with the fixture binary and isolated output paths.
- `_line_count(lines, needle)` checks duplicate aggregation rows.

## Scenarios

### Production GUI/web renderer parity evidence

#### exports an admitted Stage4 Simple binary to nested production parity checks

Checks explicit Stage4 admission, removal of binary discovery, and propagation
of the admitted binary plus renderer, event, timing, readback, and provenance
rows.

#### rejects an unreceipted browser binary

- `Reject an unreceipted browser binary`
- Expected: wrapper exits `1` with
  `production_gui_web_renderer_parity_simple_bin_status=unprovenanced`.

#### rejects a stale Stage4 receipt

- `Reject a stale Stage4 receipt`
- Expected: wrapper exits `1` with
  `production_gui_web_renderer_parity_reason=simple-bin-unprovenanced`.

#### keeps every renderer evidence entrypoint on the canonical Stage4 gate

Checks the parity wrapper, WM event wrapper, and Aetheric producer/checker all
source the canonical Stage3 facade and Stage4 provenance helper and call
`stage4_verify_candidate_provenance`.

#### prints production parity blocker summary rows for operator triage

Checks the compact summary retains surface, font, Metal, and event blocker rows.

#### rejects Rust seed Simple binary in Metal framebuffer readback evidence

Checks nested Metal evidence records a Rust seed as forbidden without executing
it.

#### selects only self hosted backend simple candidates by default

Checks the nested backend wrapper keeps its existing self-hosted candidate and
seed-rejection contract.

#### preserves explicit backend simple bin overrides in missing-bin evidence

Checks an explicit missing nested backend binary remains visible in evidence.

#### rejects explicit backend rust seed simple bin evidence

Checks the nested backend wrapper rejects an explicit Rust seed.

#### records bounded subcheck timeout evidence

Checks a timed-out nested subcheck emits typed timeout status and duration.

#### prints bounded summary output while keeping full evidence on disk

Checks verbose nested rows remain in the retained artifact rather than stdout.

#### continues independent evidence collection after layout manifest failure

Checks backend, font, Metal, and event diagnostics continue after layout
failure.

#### derives partial layout manifest counts after timeout

Checks partial case counts survive a bounded layout timeout.

#### fails top-level parity when font offload is unavailable

Checks unavailable font evidence cannot be promoted to a parity pass.

#### records Metal readback evidence even when font offload is unavailable

Checks independent Metal evidence is retained despite the font blocker.

#### forwards surface capture host and prerequisite evidence

Checks host identity, capture backend, required commands, and missing commands
are promoted.

#### emits surface manifest host and capture provenance without downstream fallbacks

Checks Tauri and Chrome capture provenance remains explicit when downstream
evidence is unavailable.

#### runs macOS Metal render-log compare when Metal readback exists even if backend row is fallback

Checks the Metal render-log comparison runs from real readback evidence rather
than a backend status shortcut.

#### fails top-level parity when Electron event routing validator details are missing

Checks shallow event counts cannot replace validator, source, payload, and UI
evidence.

#### fails top-level parity when Electron event timing or animation rows are invalid

Checks excessive timing, insufficient frames, or missing observed CSS motion
fail the aggregate.

#### passes with complete Electron Chrome backend Metal and event proof rows

Checks the complete fixture promotes exact Chrome, backend, Metal, font, event,
motion, payload, and artifact rows with no blur or tolerance.

#### finalizes partial evidence when the wrapper is interrupted

Checks the exit trap retains partial typed evidence rather than losing completed
subcheck output.

## Syntax

```sh
SIMPLE_LIB=src /absolute/path/to/current-stage4/simple test \
  test/03_system/check/production_gui_web_renderer_parity_evidence_spec.spl \
  --mode=interpreter --clean --fail-fast
```

Live renderer execution is outside this fixture manual and additionally
requires `SIMPLE_BIN=/absolute/path/to/current-stage4/simple`.
