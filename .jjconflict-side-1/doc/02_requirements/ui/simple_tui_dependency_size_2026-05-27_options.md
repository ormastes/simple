<!-- codex-research -->
# Simple TUI Dependency Size Feature Options

Date: 2026-05-27

## Option A: Dependency Refactoring First

Description: Keep the existing TUI implementation, split default TUI startup
from shared UI/app-heavy paths, and make non-terminal capabilities opt-in.

Pros:
- Matches current audit evidence.
- Lowest risk because the standalone TUI lane already works.
- Preserves existing app behavior while shrinking the startup closure.

Cons:
- Requires careful closure auditing and repeated native-build checks.
- May expose compiler/linker dependency-selection bugs.

Effort: M, about 6-10 files.

## Option B: Bottom-Up TUI Rewrite

Description: Replace the TUI app with a new minimal terminal app built only on
core ANSI/termios primitives.

Pros:
- Can produce a very small controlled entrypoint quickly.
- Removes ambiguity from the app startup path.

Cons:
- Duplicates a narrow lane that already exists.
- Does not solve the core runtime floor or unwanted platform libraries.
- Higher regression risk for existing TUI behavior.

Effort: L, about 10-18 files.

## Option C: Dual-Lane TUI

Description: Keep full TUI behavior and add an explicitly supported
`tui-min` lane with strict dependency gates.

Pros:
- Gives a C-like target without blocking richer TUI features.
- Good long-term release/test story.

Cons:
- More build/test matrix complexity.
- Requires clear capability naming and documentation.

Effort: M/L, about 8-14 files.
