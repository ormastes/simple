# Bounded Multi-Caret Manager

## Purpose

Proves the Caret agent manager owns a finite batch of child CLI processes and
does not leak ownership to its terminal presentation layer.

## Scenario: launch and stop four wrappers

The scenario creates Claude, Codex, Gemini, and Kimi launch requests, substitutes
`/bin/echo` for each executable, and admits all four into a manager with capacity
four. It requires four started process records and four derived terminal panes,
then polls and performs a terminal stop through the parent manager.

## Scenario: reject excess work

Two requests submitted to a one-slot manager must return
`capacity_exceeded` with zero process records. This proves rejection occurs
before spawning.

## Scenario: idempotent terminal cleanup

Stopping an unstarted manager twice must remain `stopped` with
`no_processes`. Partial batch launch is separately required to roll back every
returned child handle.

## Boundary

This is evidence for `caret-batch-process-adapter`. The derived
`AgentTmuxEmbed` is a display model only. It does not create an `os.apps.smux`
session or bind PTYs, so it cannot satisfy `caret-smux-multi-launch`.
