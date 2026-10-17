# Windows exact interactive input

**TEST_BLOCKED — authored manual; compilation, execution and docgen pending.**

Executable: `test/03_system/tools/smux_interactive_windows_input_spec.spl`.
Requirement: `REQ-SMUX-INTERACTIVE-002`.
Design: `doc/05_design/smux_interactive_protocol.md`.

The single live scenario requires native Windows and the real selected ConPTY
provider. Another OS or unavailable provider must fail; there is no host skip or
placeholder assertion. It has not executed and is not a PASS receipt.

1. Create a production session and spawn `cmd.exe /d /q` on its actual PTY.
2. Send `set /a 3141+2718` encoded as hex through the explicit pane input RPC.
3. Poll bounded production captures and require the computed result `5859` to
   remain absent while no Enter byte has been sent.
4. Send separate hex `0d`, require real shell result `5859`, and capture it in
   the production frame response.
5. Require PTY close to prove terminal cleanup within its bounded retry window.

The positive arithmetic result is absent from the submitted command, so input
echo alone cannot satisfy the assertion. Run with qualified rebuilt Windows
Phase2 and Phase3 producers/runners and retain actual output, assertions and
cleanup evidence before regenerating this manual. This scenario establishes
exact input delivery, not two independent rendered console clients.
