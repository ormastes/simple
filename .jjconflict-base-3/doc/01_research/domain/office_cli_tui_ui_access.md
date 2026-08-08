# Office CLI, Calc TUI, and Semantic UI Access — Domain Research

## Research Question

What external conventions support a debuggable office TUI that can be operated
by people and LLM tools while still providing reliable system-test evidence?

## Command-Line Contract

The Open Group's POSIX utility documentation distinguishes options from
operands and requires utilities to diagnose unrecognized options with a
non-zero exit status. It also treats a utility's synopsis and option
description as the authoritative command contract.

For this feature, that supports:

- an explicit, documented `simple office calc [FILE] --tui` synopsis;
- preserving `--tui` until the Office command owner parses it;
- deterministic diagnostics and exit status for invalid combinations;
- documenting legacy aliases separately from the preferred route.

Sources:

- [POSIX utility introduction](https://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap01.html)
- [POSIX utility argument conventions](https://pubs.opengroup.org/onlinepubs/9699919799/basedefs/V1_chap12.html)

## Semantic UI Representation

WAI-ARIA defines an interoperable UI model in terms of roles, states, and
properties. It emphasizes that roles describe what a component is, while
states and properties communicate its current interactive value, selection,
or focus. Although Simple's protocol is not a browser ARIA API, the same
principle applies to a TUI automation surface:

- a cell should be a stable semantic node, not only painted characters;
- focused/selected/editing state should be explicit;
- formula input should expose its value and supported actions;
- action results should be observable in a later snapshot.

This makes the surface useful to accessibility tools, debuggers, tests, and LLM
operators without coupling them to terminal coordinates.

Sources:

- [WAI-ARIA 1.2](https://www.w3.org/TR/wai-aria/)
- [WAI technique for exposing UI component roles](https://www.w3.org/WAI/WCAG22/Techniques/aria/ARIA4)

## Terminal Interaction and Capture

A pseudo-terminal is the appropriate boundary when a test must prove terminal
behavior: it gives the child process terminal semantics and allows the driver
to send real input bytes. The node-pty project documents the core property:
forking a process with pseudoterminal file descriptors so programs emit their
terminal control sequences.

tmux documents a complementary evidence pattern:

- `send-keys` injects keystrokes as terminal input;
- `capture-pane` captures the visible pane;
- capture can preserve terminal attributes or include history.

This supports using a PTY/TUI driver for launch and screen evidence. However,
the captured pane is visual evidence, not sufficient behavioral proof by
itself. Semantic `snapshot/find/act/history` assertions should remain the
source of truth for cell identity, formula input, result values, and action
correlation.

Sources:

- [Microsoft node-pty](https://github.com/microsoft/node-pty)
- [tmux advanced use: sending keys and capturing panes](https://github.com/tmux/tmux/wiki/Advanced-Use)

## Applied Guidance

The resulting test strategy is deliberately dual:

1. Use the deployed CLI and a real terminal boundary to prove launch,
   keystroke compatibility, ANSI rendering, and clean shutdown.
2. Use the canonical semantic UI protocol to prove discovery, stable targets,
   value-bearing actions, independent post-state, and bounded history.

For formulas, the system test should choose values whose results are obvious:

```text
A1 = 6
A2 = 8
B1 = A1*A2       -> 48
C1 = AVG(A1:A2)  -> 7
```

This avoids ambiguous rounding while proving both operator precedence and the
`AVG()` function-call alias through the real application.

## Conclusion

External CLI, accessibility, and terminal-testing conventions all point to
the same design: explicit command ownership, semantic roles/state/actions as
the automation contract, and PTY screen capture as supplementary evidence.
