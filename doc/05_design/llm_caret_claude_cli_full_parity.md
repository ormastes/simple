# LLM Caret Claude CLI Full Parity - Detail Design

Date: 2026-07-05

## Matrix-Driven Implementation

Implementation proceeds from three generated matrices:

- `doc/03_plan/trace/llm_caret_claude_cli_full_parity_feature_matrix.tsv`
- `doc/03_plan/trace/llm_caret_claude_cli_full_parity_file_matrix.tsv`
- `doc/03_plan/trace/llm_caret_claude_cli_full_parity_symbol_matrix.tsv`

Each implementation task chooses one feature row, then completes every file row
and symbol row belonging to that feature. A row is complete only when:

1. the target Simple file exists;
2. the target file LOC is at least the source LOC recorded in `target_min_loc`;
3. every symbol row has an implemented Simple symbol or documented data
   structure with equivalent behavior;
4. unit tests cover the file-local behavior;
5. a system SSpec covers the user/operator behavior;
6. generated `doc/06_spec` manual output has `0 stubs`;
7. the row status is updated by evidence, not by intent.

## Implementation Phases

### P0: Inventory and Gate Foundation

- Keep matrices generated from the current Claude source tree.
- Add row-status columns only after implementation starts.
- Add a full-parity checker that compares source tree counts, matrix rows,
  target file existence, target LOC, symbol existence, and test evidence.

### P1: Core CLI Runtime

Implement entrypoints, QueryEngine, Tool, Task, schemas, bootstrap state,
constants, CLI printing, structured IO, NDJSON, cost tracking, token budgets,
and command-line parsing. These become the stable execution substrate.

### P2: Tools and Slash Commands

Implement every `commands/**` and `tools/**` row. Each command gets:

- parser/validator;
- permission model;
- deterministic fake-backed execution;
- real execution adapter where required;
- help/status output;
- unit and system SSpec coverage.

### P3: Terminal UI

Port Ink/components/screens/hooks/vim/buddy/voice behavior into Simple TUI
widgets and capture-backed SSpec manuals. React implementation details are not
copied, but visible behavior, state transitions, keybindings, and accessibility
semantics are mandatory.

### P4: Remote Bridge and Server

Implement bridge, remote, trusted-device, session-runner, transport, MCP, and
server rows. Default tests use local fake transports; live tests are opt-in and
credential-gated.

### P5: Services, Plugins, Skills, Memory, Output Styles

Implement API services, plugin loading, skill discovery, memory directory
handling, migrations, output styles, telemetry, and background task services.
All filesystem/process/network operations use owner facades.

### P6: Support Utilities and Platform Hardening

Implement every `utils/**`, `context/**`, `state/**`, `native-ts/**`, and
platform helper row. Shared helpers may be factored, but every original symbol
row must still point to the helper and have tests.

### P7: Integration Shell

Wire `claude_full` into the existing `llm_caret` facade behind an explicit
provider flag. Run side-by-side parity suites against compact wrapper behavior
and full Claude-compatible behavior.

### P8: Completion Audit

Run:

- full-parity plan checker;
- every row-level unit test;
- every feature-level system SSpec;
- generated manual docgen;
- direct runtime/env guard;
- source/file/symbol coverage audit;
- size parity audit.

No row can be marked done by search absence, optimistic summary, or skipped
host capability.
