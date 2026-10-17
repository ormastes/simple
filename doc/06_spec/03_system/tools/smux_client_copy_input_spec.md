# SMUX incremental copy input

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/03_system/tools/smux_client_copy_input_spec.spl`.
Requirement: **REQ-SMUX-INTERACTIVE-005**, traced in all 11 unexecuted scenarios.

The production pure decoder consumes coalesced or fragmented copy-mode input.
It emits ordered action names and retains only an unfinished escape sequence.
It has no child-input action and performs no clipboard or history operation.

| Input | Action |
|---|---|
| k / Up arrow | up |
| j / Down arrow | down |
| Page Up / Page Down | page-up / page-down |
| q | exit |
| Space | mark |
| CR, LF or y | copy |
| Standalone Escape plus explicit deadline flush | exit |

1. Decode `kkq` in one chunk into up, up, exit.
2. Decode multiple arrows and page sequences from a single chunk in order.
3. Receive Escape, bracket and arrow final byte separately. Preserve pending
   state until the complete arrow arrives; do not exit prematurely.
4. Receive a page key in fragments with ordinary keys around it. Preserve
   both sequence and action ordering.
5. Retain standalone Escape through an empty read, then emit exit exactly
   once when the controller explicitly flushes it after its deadline.
6. Do not flush a partial CSI as standalone Escape. It can still complete.
7. Emit mark and copy actions for Space, Enter and y. These are intent only.
8. Ignore unknown complete CSI sequences and resume ordinary navigation.
9. Clear overlong pending CSI and malformed sequences; pending state stays
   bounded to sixteen bytes.
10. Ignore unrelated Unicode and unknown Escape bindings. Emit no child input.
11. Complete a pending arrow without mutating the original state value.

`flush_escape=true` resolves a previously pending bare Escape before new data;
an Escape newly received in that call waits for a later flush. The controller
owns its 100 ms deadline. This pure spec does not prove elapsed time, actual
keys, visible copy navigation, clipboard transfer or shell input isolation.

After runtime admission, execute the spec, generate the mirrored manual with
zero stubs and run `sspec-maintain scan`, preserving runtime identity, executed
counts, exit status and artifacts. None of those gates has run yet.
