# LLM Caret Claude CLI Full Parity — System Test Plan

Date: 2026-07-25

## Scope

This is the strict completion plan for `REQ-LLM-CARET-FULL-001..007` and
`NFR-LLM-CARET-FULL-001..005`. It covers the historical Claude source
inventory, every mapped Simple target, focused owner behavior, the shipped
Caret CLI, and the terminal UI. It does not convert a static matrix, source
ledger, LOC floor, or zero-execution manual into behavioral PASS evidence.

## Current authoritative state

The 2026-07-25 one-shot gates report:

| Evidence | Current result | Completion meaning |
|---|---:|---|
| Historical file matrix | 1,902 rows | Inventory only |
| Historical feature matrix | 599 rows | Inventory only |
| Historical symbol matrix | 14,119 rows | Inventory only |
| Provenance-pinned `tmp/claude/claude-code-main/src` | Missing | Current-upstream parity unprovable |
| Existing mapped target files | 745 / 1,902 | 1,157 targets still missing |
| Targets meeting required LOC | 563 / 1,902 | Strict size gate red |
| Targets meeting 80% source LOC | 600 / 1,902 | 1,302 below the floor |
| Class target files | 124 / 124 | File existence only, not behavior |
| Qualified self-hosted `bin/simple` | Missing | SSpec/docgen execution blocked |
| Qualified cached native Caret | Missing | CLI/PTY execution blocked |

The exact public package `@anthropic-ai/claude-code@2.1.218` was fetched from
the npm registry for provenance review. Its tarball SHA-256 is
`3a434c8bcb493e9ca87315d9aa6064835c5987e8fbc85c181bb76157dd5c45d8`;
it contains seven package entries and no `src/` tree. It cannot replace the
required pinned source inventory.

At the start of this continuation, `claude_full` contained 848 source files,
349 executable specs, and 1,564 lexical `it` scenarios. Only 69 specs had
mirrored manuals and 14 carried the modern Codex system-test marker. Those
counts are a modernization backlog, not evidence that all scenarios execute or
assert direct behavior.

## Authoritative executable specs

| Executable spec | Manual | Purpose | Current state |
|---|---|---|---|
| `test/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.spl` | `doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_traceability_spec.md` | Direct 25-file Caret map | Modernized; checker passes independently; SSpec unexecuted |
| `test/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.spl` | `doc/06_spec/03_system/tools/llm/llm_caret_claude_cli_full_parity_implementation_spec.md` | Strict pinned-source/file/LOC/class release gate | Intentionally red |
| `test/03_system/app/llm_caret/feature/llm_caret_cli_hardening_spec.spl` | Mirrored app manual | Shipped CLI process and cached-wrapper contract | Runtime blocked |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_hidden_feature_spec.spl` | Mirrored app manual | Component TUI and hidden admission | Static/manual only |
| `test/03_system/app/llm_caret/feature/llm_caret_tui_pty_spec.spl` | Mirrored app manual | Real cached-wrapper PTY lifecycle | Artifact blocked |
| Focused `test/03_system/tools/llm/claude_full/**/_spec.spl` | Same relative path under `doc/06_spec/03_system/tools/llm/claude_full/` | Parts-bin owner behavior | Incremental; many manuals and direct owners remain missing |

The older plan names `full_parity_inventory_spec.spl`,
`core_cli_runtime_spec.spl`, `commands_tools_spec.spl`,
`terminal_ui_spec.spl`, `remote_bridge_spec.spl`,
`services_plugins_skills_spec.spl`, and `support_utilities_spec.spl` do not
exist. They are not evidence. Their intended coverage must be supplied by real
focused specs or by reviewed aggregate specs created in future lanes.

## Requirement traceability

| Requirement | Required evidence | Current status |
|---|---|---|
| FULL-001 file inventory | Pinned tree plus exact file matrix | Missing pinned tree |
| FULL-002 symbol inventory | Pinned tree plus exact symbol rows and direct tests | Historical rows only |
| FULL-003 feature capsules | Nonempty target capsule and real spec per feature | Partial |
| FULL-004 no incomplete rows | Zero missing/untested rows | Fails |
| FULL-005 LOC/evidence floor | 1,902 targets meet accepted gate | Fails |
| FULL-006 no skipped features | Every row implemented or explicitly red | Red rows retained |
| FULL-007 progress report | Exact file/80% counts in plan/report | Present above |
| FULL NFR-001 architecture | Reviewed MDSOC ownership | Partial |
| FULL NFR-002 deterministic verification | Offline fixtures and no paid calls | Present for focused lanes |
| FULL NFR-003 hot-path discipline | No repeated tree scan in requests | Needs full owner review |
| FULL NFR-004 observability | Typed state/effect evidence per feature group | Partial |
| FULL NFR-005 matrix authority | Checker and spec require exact rows/PASS | Present but red |

## CLI-first execution order

1. Restore a provenance-pinned Claude source tree and regenerate the three
   matrices. Do not accept the npm binary package as source.
2. Modernize shipped CLI roots and direct provider transports before
   parts-bin TUI breadth: `main`, Claude/OpenAI/OpenAI-compatible send paths,
   OpenCode spawn/send, local torch, config loading, and structured CLI I/O.
3. Close bridge/MCP direct owners with deterministic state/effect seams,
   canonical matchers, and synchronized zero-execution manuals.
4. Qualify a current pure-Simple runtime and execute the direct trace,
   full-parity red gate, focused CLI specs, and docgen once.
5. Build a cached native Caret with source/runtime/binary provenance and run
   promptless CLI plus hidden admission without provider credentials.
6. Execute component TUI, then real PTY routing/editing/geometry/lifecycle.
7. Regenerate manuals, require zero stubs, and rerun final static release gates
   only after their inputs change.

## Pass/fail criteria

Completion requires all of the following:

- the pinned source plan checker exits zero with exact file/feature/symbol rows;
- all 1,902 targets exist and satisfy the accepted implementation/evidence gate;
- every mapped declaration has a direct behavior assertion or a reviewed
  non-applicability justification;
- every changed SSpec executes with real assertions and produces a current
  manual with `0 stubs`;
- CLI and PTY wrappers run the provenance-checked cached artifact with no source
  or Rust-seed fallback;
- hidden default/enabled/disabled/false cases create no model or persistence
  effects;
- `find doc/06_spec -name '*_spec.spl'` returns zero files.

Any missing tree/artifact, nonzero checker/test exit, zero executed examples,
placeholder assertion, stale manual, or unsupported current-upstream claim is
a failure, not a skip.

## Manual and capture policy

Primary CLI/TUI flows stay visible; exhaustive matrices and helper source are
folded. Zero-execution manuals must say so explicitly. CLI evidence records
stdout, stderr, exit, isolated HOME, and binary/runtime hashes. TUI evidence
uses the canonical PTY artifact tree under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_tui_pty/` and
must preserve pre/post terminal state.
