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

## 2026-07-25 superseding scope and provenance evidence

The active user objective now explicitly includes CLI, TUI, hidden features,
and checking every Claude function, so the earlier exclusion no longer defines
completion. It remains useful only as the first CLI-hardening phase.

The exact public npm package `@anthropic-ai/claude-code@2.1.218` was inspected
without executing it. Tarball SHA-256:
`3a434c8bcb493e9ca87315d9aa6064835c5987e8fbc85c181bb76157dd5c45d8`.
It contains seven entries (`cli-wrapper.cjs`, `install.cjs`, platform binary,
package metadata, license, README, and SDK declarations) and no `src/` tree.
Therefore the public package can support installed-binary compatibility probes
but cannot regenerate or validate the historical 1,902-file source inventory.
