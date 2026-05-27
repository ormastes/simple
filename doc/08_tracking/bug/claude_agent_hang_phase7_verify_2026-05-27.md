# BUG: Claude Code sub-agent hangs during Phase 7 verify of SStack pipeline

**Date:** 2026-05-27
**Status:** OPEN
**Severity:** Medium (blocks pipeline completion, requires manual intervention)
**Component:** Claude Code Agent tool / SStack orchestrator

## Problem

During the `pure-db-perf-improve` SStack pipeline, the Phase 7 (verify) agent
hung indefinitely after being spawned via the Agent tool.  The user had to
interrupt the tool call manually.  The agent never returned a result or error.

## Context

- Phases 1-6 all completed successfully via Agent tool spawns
- Phase 7 agent was spawned with a verify prompt containing 4 test commands
  and 6 AC verification steps
- The agent appeared to hang — no progress, no timeout, no error
- The `bin/simple` symlink was missing at the time (broken by setup state),
  which may have caused the agent to enter an unrecoverable state if it
  attempted to run tests and failed silently

## Reproduction

1. Run an SStack pipeline with 8 phases via Agent tool spawns
2. Break `bin/simple` symlink between Phase 6 and Phase 7
3. Spawn Phase 7 agent — it may hang instead of reporting the missing binary

## Workaround

- Cancel the hung agent (user interrupts tool call)
- Run Phase 7 verification inline (directly in orchestrator context)
- Ensure `bin/simple` symlink exists before spawning agents:
  `sh scripts/setup.sh`

## Root Cause Hypothesis

Two possible causes:

1. **Missing binary + silent failure:** Agent ran `bin/simple test ...` which
   returned "No such file or directory", and the agent entered a retry loop
   or stalled processing the unexpected error.

2. **Agent context exhaustion:** The verify agent prompt was large (4 test
   commands + 6 grep verifications + report creation).  Combined with reading
   multiple files, the agent may have hit its context limit and stalled.

## Proposed Fix

- SStack orchestrator should verify `bin/simple` exists before spawning any
  agent that runs tests.  Add a pre-flight check:
  `if not file_exists("bin/simple"): run scripts/setup.sh`
- Agent prompts for verify phases should include an explicit early-exit
  instruction: "If bin/simple is not found, report the error and exit
  immediately."
- Consider adding a timeout to Agent tool calls for SStack phases (e.g.,
  10 minutes max).
