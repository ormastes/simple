<!-- codex-design -->
# TUI Design: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Layout

Three-column companion layout:

1. left rail: session list and mode chips
2. center: selected session timeline and child-task tree
3. right rail: digest, blockers, notifications, and bridge health

## Primary Views

### Session Overview

- session name/objective
- status
- wake reason
- child-task counts
- stale/live indicator

### Timeline View

- ticks
- signals
- quiet decisions
- delegated actions
- failures
- notifications

### Task Tree View

- parent session at root
- nested child tasks with status and resource policy
- final summaries on completed tasks

### Digest View

- last brief
- retained facts
- open blockers
- suggested next actions

## Interaction Model

- keyboard-first selection between sessions, timeline, and task tree
- summary/detail toggle
- filter by severity, wake type, or status
- visible disabled controls in replay-only mode

## States

- attached/live
- replay/import
- paused
- backpressure active
- degraded bridge

## Design Principle

The screen should always answer:

- what is the assistant doing now
- why did it wake up
- what child tasks exist
- what is blocked
- what can the operator do next
