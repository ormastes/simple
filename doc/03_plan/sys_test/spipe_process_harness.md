<!-- codex-design -->
# SPipe Process Harness System Test Plan

## Scope

The first test layer is pure SPipe/unit coverage for the common harness library.
Provider live-client tests are intentionally excluded from the first commit
because the deploy command emits reviewable snippets instead of mutating live
Codex, Claude, or Gemini settings.

## Requirement Trace

| Requirement | Test file | Assertions |
|-------------|-----------|------------|
| REQ-001 | `test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl` | provider normalization and provider hook event lists |
| REQ-002 | `test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl` | JSONL hook envelope contains provider, event, session, model, and escaped raw payload |
| REQ-003 | `test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl` | deploy snippets exist for Claude, Codex, and Gemini with expected paths |
| REQ-004 | `test/system/app/spipe_process_harness/feature/spipe_process_harness_spec.spl` | HUD renders model, jj, commit, hr, week, and goal fields |
| REQ-005 | `test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl` | default and feature-specific state/event paths |
| REQ-006 | both SPipe spec files | missing state, missing approval, explicit block marker, and approved allow path |

## Test Cases

1. Provider normalization:
   - `Claude Code` -> `claude`
   - `Codex GPT` -> `codex`
   - `Google Gemini` -> `gemini`
   - unknown providers remain stable after lowercase/trim normalization

2. Hook event metadata:
   - Claude includes `PreToolUse` and `SessionStart`
   - Codex includes session/tool/turn lifecycle events
   - Gemini includes session/tool/prompt lifecycle events

3. Hook event envelope:
   - includes normalized provider
   - includes event
   - includes session id
   - includes model
   - preserves raw payload as a JSON string

4. State and prevention:
   - blank state blocks
   - approval-required state without `User Approved: true` blocks
   - `Prevent: block` blocks even when approval exists
   - `STATUS: FAIL` blocks
   - approved allow state returns exit code `0`

5. HUD:
   - one-line output includes `model=`, `jj=`, `commit=`, `hr=`, `week=`,
     and `goal=`

6. Deploy:
   - generated snippets include all three providers
   - generated paths are under `.spipe/hook-deploy/`
   - live provider settings are not overwritten by pure rendering tests

## Commands

Focused verification:

```bash
bin/release/simple test test/unit/lib/spipe_process_harness/spipe_process_harness_spec.spl --fail-fast
bin/release/simple test test/system/app/spipe_process_harness/feature/spipe_process_harness_spec.spl --fail-fast
```
