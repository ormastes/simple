# Windows native provider composition

**TEST_BLOCKED: authored manual; execution and docgen pending.**

Requirement: `REQ-SMUX-WINDOWS-NATIVE-PROVIDER-SELECTION`.
Executable: `test/01_unit/compiler/driver/windows_native_provider_composition_spec.spl`.
Design and native fixture commands:
`doc/07_guide/tooling/smux_windows_native_composition.md`.

These six scenarios invoke the production source-root resolver against actual
source files. No scenario below has been executed or is a PASS receipt.

| Scenario | Required result | Status |
|---|---|---|
| Stable public PTY import | First Windows overlay owns `std.sys.pty` | TEST_BLOCKED |
| Canonical library PTY spelling | Same overlay owns `lib.sys.pty` | TEST_BLOCKED |
| Explicit synchronous SOSIX TCP import | Overlay owns only that selected capsule | TEST_BLOCKED |
| SFFI network outside overlay | Existing HTTP/UDP containing source module remains selected | TEST_BLOCKED |
| Overlay absent | Default PTY and SOSIX sources remain selected | TEST_BLOCKED |
| Roots reordered | Exact default modules win when their root comes first | TEST_BLOCKED |

The separate source fixture imports the stable PTY and SOSIX network APIs and
must compile/run using qualified Phase2 and then Phase3 producers. Its invalid
arguments check selection and error contracts; successful execution does not
prove live ConPTY or TCP behavior. Provider and smux system scenarios retain
those runtime obligations. Preserve selected physical closure/HIR paths,
producer hashes, source snapshots, linked runtime identity and actual assertion
counts before regenerating this manual and marking any scenario PASS.
