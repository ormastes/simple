# Domain Research: Current-State Build Progress

Mature build systems separate durable event history from a bounded current-state view. Bazel Build Event Protocol, Ninja status output, Cargo JSON messages, and BuildKit progress all provide structured events, while dashboards maintain a compact materialized view for inexpensive polling. The reusable pattern is:

1. append immutable detailed events for audit and debugging;
2. atomically replace one bounded snapshot for current status;
3. identify the writer/build and enforce monotonic sequence numbers;
4. report unknown/low-confidence ETA explicitly;
5. retain phase-specific information such as linker state without requiring log parsing.

Simple should use its typed SDN-style records and centralized worktree storage rather than introducing a database or JSON parser into the compiler nucleus.

