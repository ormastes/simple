# SPipe lifecycle inventory

Inspected 2026-11-06 at upstream commit `79bb6317f7aa1a201df26665b677aa3dc3766781`.

## Authority and workspace

The supplied [complete proposal](../04_architecture/spipe_complete_lifecycle.md) remains proposed, not evidence of implementation. Work proceeds on `work/spipe-lifecycle-20261106` in `C:/dev/spipe-lifecycle-20261106`. The external session record is `C:/dev/spipe-lifecycle-20261106-session.sdn`. The original Simple submodule contains unrelated deletions and MCP edits and is preserved.

## Existing integration points

- `cli/spipe.js` dispatches existing `doctor`, release, review and fine-tuning operations. Lifecycle must be a separate command group; existing doctor behavior remains compatible.
- `src/cli/release_commands.js` and `src/release/` separate adapter dispatch from reusable domain logic. Review logic similarly lives in `src/review/`.
- `src/spipe_cli/` and `src/spipe_mcp/` contain Simple entrypoints; `test/spipe_cli_parity_spec.spl` and `test/spipe_mcp_handshake_spec.spl` cover their contracts. New capabilities must account for both surfaces.
- `scripts/build.sh` validates required paths and plugin projections and optionally exercises the Simple runtime. Its optional runtime skip is not proof of Simple parity.
- `plugin/` distributes CLI, MCP, domain modules and provider skills. New modules require synchronized projections through the existing distribution mechanism.
- `skills/index.md` defines common checkout resolution and scope authorization before knowledge traversal. The lifecycle inventory must never discover private workspace scopes implicitly.
- `doc/00_llm_process/skill_command/vcs_session_policy.md` requires owned isolated worktrees, exact target/head evidence and protected integration.
- Existing Node unit/integration tests use `node:test`; existing Simple acceptance specs must remain executable, with generated manuals under `doc/06_spec`.

## Confirmed migration constraints

- `src/spipe_cli/main.spl` explicitly labels its implementation stage 1 and rejects unported commands with exit 3. `bin/spipe` first admits a hash-checked native executable and then has an interpreter fallback. npm instead exposes `cli/spipe.js`. A lifecycle feature must state which surface implements it and test unsupported surfaces fail closed; a Node-only success cannot establish Simple support.
- `scripts/build.sh` invokes `scripts/project-self-review-guidance.js --check` and named Node test files. New tests must be included in the actual build gate rather than merely added to disk.
- `doc/00_llm_process/spipe/loop.md` describes up to ten iterations. The host instructions cap verify/fix cycles at six and prohibit rerunning green criteria. This is an actual policy inconsistency to inventory and reconcile through canonical guidance, not an invitation to run either loop now.
- The canonical SStack document carries a generated-source marker and describes eight phases with fresh phase agents; the packaged skill expresses a bounded eight-phase process. The proposal's thirteen capability phases need an explicit compatibility mapping rather than silently replacing SStack.

## Remaining inspection

No lifecycle command, doctor or session implementation was found in the initial tracked-filename inventory. This is a discovery finding, not an exhaustive implementation audit. Next inspection must cover generated markers, projection scripts, canonical skill contracts, the agent loop, authorization and parser reuse before designing replacements.

External references in the supplied proposal have not been verified. No empirical or current upstream API claim is made from them here. Requirements selection remains a prerequisite to implementation; no passing gates or test results have been claimed.
