# Phase-2 Source-Reclaim Exact-Body Contracts

The focused helper imports the lightweight probe module without invoking
`main()` or `rt_string_free`.

It verifies that:

- the current `CompilerDriver.compile` body has singular parse → gate → release
  → reclaim → eviction → lower ordering;
- `CompileContext.source_contents_reclaimable` requires low-memory mode and a
  non-VHDL backend;
- `lexer_release_parse_source_globals` contains all seven exact cleanup lines;
  and
- negative-control sources cannot pass by placing matching tokens in
  docstrings or sibling methods.

This helper checks source-contract parsing only. Runtime alias ownership remains
release-blocking in the bounded shell gate and requires exactly `1` then `0`.
