# Rust Seed Accepts Reserved `on` Identifier

The Rust seed accepted `val on = ...` in `src/os/hosted/hosted_entry.spl`, while
the stage3 pure-Simple discovery parser rejected it with `expected pattern,
found On`. Source checks performed only with the seed therefore produced a
false green result.

Production code now uses `fullscreen_enabled`. Parser conformance should add a
shared negative fixture so seed and self-hosted frontends reject reserved
identifiers consistently with a source location.
