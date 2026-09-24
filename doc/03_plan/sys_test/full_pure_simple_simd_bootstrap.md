# Full Pure-Simple SIMD Bootstrap System Test Plan

Status: Active

## Trace matrix

| Scenario | Requirements | Evidence |
|---|---|---|
| Scalar and forced-backend semantic parity | REQ-SIMD-001..004, NFR-SIMD-008 | Cross-backend result hashes and strict unsupported-backend failures |
| Platform-neutral DB scan/filter | REQ-SIMD-005..007, NFR-SIMD-001..003,009 | Correctness hash plus locked scalar/SIMD benchmark receipt |
| Platform-neutral HTTP classify/parse | REQ-SIMD-005..007, NFR-SIMD-001..004,009 | Correctness hash, p99, and throughput receipt |
| Trusted four-stage bootstrap | REQ-SIMD-008,010, NFR-SIMD-006 | Per-stage artifact identity and essential-tools smoke receipt |
| Cached Simple/MCP deployment and rollback | REQ-SIMD-009, NFR-SIMD-005,007 | Exact artifact hashes, startup/request/RSS report, rollback receipt |
| Compiler/interpreter phase suite | REQ-SIMD-010..012, NFR-SIMD-010..011 | Phase matrix with all supported unit/integration/system/doctest commands |
| MCP, LSP MCP, SPipe, DevHub, and Caret phase suite | REQ-SIMD-011..012 | Per-phase tool-suite results; unsupported rows remain explicit and fail closed |
| Phase 1/2 major-feature modes | REQ-SIMD-010..012,015, AC-06..09 | Fixed paired interpreter/native rows for compiler, language/runtime, MCP, LSP MCP, T32 MCP, SPipe/SSpec, Caret, Slang, and SIMD DB/web; exact generation/admission/provenance and CPU/job evidence |
| Actual launches and SPipe plugin at every phase | REQ-SIMD-015, AC-09 | Eight live rows per phase, exact artifact/plugin admission hashes, process identity, protocol/fixture assertion and shutdown outcome |
| DevHub GitHub/Jira/Confluence access at every phase | REQ-SIMD-015, AC-09 | Independent authenticated known-resource reads, expected provider/fixture identity, sanitized result hashes; configuration-only and unsupported identity checks remain non-passing |
| Cross-target availability | REQ-SIMD-002..004, AC-07 | Native/emulated receipts or blocked rows with exact resume information |
| Final production verification | REQ-SIMD-013..014, NFR-SIMD-010..012 | Requirement matrix and `STATUS: PASS` |

## Scenario rules

- Execute each scenario through SPipe/SSpec with real assertions and built-in matchers.
- Bind every bootstrap scenario to an exact compiler path and SHA-256; never inherit `SIMPLE_BINARY` or `SIMPLE_BIN` as authority.
- A phase runs only commands supported by its admitted capability manifest. Missing support is recorded as unsupported with a resume command and never counted as PASS.
- The phase-suite scenario enumerates compiler, interpreter, MCP, Simple LSP MCP, SPipe/SSpec, DevHub, and LLM Caret explicitly so a missing suite cannot disappear from aggregate output.
- Pair each suite with actual launch/capability sanity. The live controller's `mcp`, `lsp_mcp`, `spipe_plugin`, `caret`, `devhub`, `github`, `jira`, and `confluence` rows run for each phase using that phase's frozen manifest. Compiler/interpreter semantic checks remain separately required.
- Phase 1/2 major-feature rows use
  `scripts/check/check-bootstrap-phase-feature-matrix.py`. Missing rows fail;
  declared unsupported/blocked rows retain ownership and exact resume argv. A
  stale generation, row hash pin, provenance, admission, relative launcher, or
  script/PATH wrapper fails before process launch even if an ambient tool would
  pass.
- Negative controller fixtures cover missing/cross-phase/stale admission, zero-work startup, protocol errors, output/time limits, unconfigured providers, malformed/error JSON, wrong fixture identity, and input drift. Their PASS proves the controller only; actual launch/access requires live admitted artifacts and existing read credentials.
- `devhub auth status` is not an auth oracle: its current implementation returns zero even when unconfigured. A known Jira issue and Confluence page must actually be read through the phase's DevHub artifact. Missing identity/capability routes remain visible as unsupported subchecks.
- Retain selected-backend identity and correctness hashes alongside performance data.
- Run an unchanged green acceptance command once. Stop after three distinct verify/fix cycles.

## Required phase fields

`phase`, compiler/artifact paths and SHA-256, provenance, capabilities, suite,
plugin manifest/tree digest, command/argv hash, launched process identity,
protocol/provider/known-fixture assertion, credential-source label (no secret),
status, exit/timeout/duration/max RSS, input/log/receipt hashes, owner/reviewer,
prerequisite/blocked reason, isolated roots, and exact resume command. Live
controller receipts supplement the phase matrix; missing fields remain pending
evidence instead of being fabricated.

## AVX-512 semantic exceptions

- Fixed-width f32x16, f64x8, and i32x16 gather and permute must show their
  corresponding EVEX opcode in native pipeline evidence.
- Scatter retains the ordered lane implementation unless index uniqueness is
  proven before selection or checked at runtime. This preserves deterministic
  last-writer behavior for duplicate indices; an unconditional VSCATTER is not
  conforming evidence.
- Vec16i associative reductions use vector permute/combine stages. Floating
  reductions retain ordered lane evaluation because reassociation changes
  rounding and NaN behavior.
- Dynamic lane broadcast performs its bounds check and scalar lane read before
  an AVX-512 broadcast. The emitted broadcast and the trap path are both tested.

Use `python scripts/check/check-bootstrap-phase-live.py --manifest
<absolute-phase-manifest.json> --output <new-absolute-receipt-directory>
--timeout 30` after phase artifact admission. Store the exact argv in each row;
use `--row <name>` only for a specific changed/failed row. Unsupported phase rows
remain incomplete coverage and cannot be summarized as a complete feature PASS.

## Release gate

The final candidate must pass the Stage 4 essential-tools smoke, compiler/lib/MCP/LSP checks, MCP stdio integration, complete phase matrix, full release-bound SPipe suite, environment/process facade audits, documentation freshness checks, and the Profile 2 benchmark gates before `STATUS: PASS` may be reported.
