# LLM Caret Claude CLI Harden - Domain Research

Date: 2026-07-05

## Findings

Claude-like coding CLIs typically separate:

- non-interactive prompt execution;
- model/session/config flags;
- response and stream normalization;
- tool/provider dispatch;
- local session history;
- optional remote control, OAuth, and UI surfaces.

## Chosen Domain Scope

This lane keeps only the CLI/provider/core response concepts. Remote control,
OAuth, React/Ink UI parity, and full agent orchestration are excluded until a
follow-up requirement selects them.
