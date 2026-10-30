# Caret multiplexer/TUI domain research

2026-10-25. Primary documentation checked by web search. Statements below are limited to the cited sources; proposed abstraction choices are inferences.

- [tmux control-mode documentation](https://github.com/tmux/tmux/wiki/Control-Mode): tmux can communicate with a client using text instead of drawing its terminal. This supports a programmatic tmux adapter; it does not supply an arbitrary Simple widget renderer.
- [tmux control protocol in the official OpenBSD manual](https://man.openbsd.org/OpenBSD-current/man1/tmux.1): each command response has begin/end-or-error framing; notifications occur outside response blocks. A stream adapter must separate correlated responses from asynchronous events. Client-size reporting is explicit.
- [tmux command manual](https://man.openbsd.org/tmux): pane and window resizing are separate operations, and pane zoom is a toggle that changes visible window occupancy. The adapter must preserve actual resize and zoom semantics rather than only changing a Caret flag.
- [Microsoft pseudoconsole documentation](https://learn.microsoft.com/en-us/windows/console/pseudoconsoles): ConPTY exchanges UTF-8 terminal data. Raw terminal bytes, text scalars and display cells remain different units in the API.
- [Microsoft ResizePseudoConsole documentation](https://learn.microsoft.com/en-us/windows/console/resizepseudoconsole): resizing changes the pseudoconsole dimensions visible to console applications. A layout metadata update alone therefore does not establish a resized child.

## Inferred design consequences and pitfalls

Use a core mux API for background sessions and pane processes, then a narrow optional TUI extension for terminal layout/presentation. A general UI extension would broaden the contract to widget semantics, coordinate systems, accessibility and render surfaces that tmux is not designed to own; reuse Simple's existing UI architecture for that future scope.

Control-mode integration needs a real framed stream parser, command correlation, bounded event queues, output backpressure and reconnect reconciliation. Avoid parsing human status output for core state. Preserve a strict legacy CLI/format adapter where existing Caret commands require it.

Layout geometry must name its units and owner: terminal cells versus pixels, pane content versus borders, logical versus rendered size, and window layout versus client viewport. Unicode width and multi-client size policies can differ; negotiate/declare them and test observed child dimensions. Preserve an unzoomed layout snapshot and original reference coordinates, including after failed child startup.

In-band terminal input cannot reliably be an independent host-widget event bus. Keep Caret semantic UI input distinct from child bytes, named keys, paste, prefix handling and host focus. Filter untrusted notification controls before rendering and do not allow transport acknowledgments to masquerade as visible delivery.

Capability discovery is advisory and version/owner-scoped. A changing backend can still reject a formerly supported operation. Record unsupported versus transport failure distinctly; never convert either to a successful no-op or silently migrate live sessions to another backend.
