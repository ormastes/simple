# SMUX interactive default key state machine

**Status: authored manual; execution and docgen pending (TEST_BLOCKED).**
Source: `test/03_system/tools/smux_client_input_spec.spl`.
Requirement: **REQ-SMUX-INTERACTIVE-001** — all 15 scenarios carry this trace.
None has executed. Assertions call the production pure decoder, without a
terminal, process substitute, clipboard or controller side effect.

`client_input_feed(state, data)` returns the next immutable prefix state and
ordered actions. `input` actions preserve exact bytes. Control actions have
empty data; the controller owns their execution and copy-mode policy.

| Default input | Action |
|---|---|
| Ctrl-B, d | detach |
| Ctrl-B, % | split-vertical: side by side columns |
| Ctrl-B, double quote | split-horizontal: upper/lower rows |
| Ctrl-B, c | new-window |
| Ctrl-B, n | next-window |
| Ctrl-B, o | next-pane |
| Ctrl-B, space | cycle-layout |
| Ctrl-B, [ | copy-mode |
| Ctrl-B, k | copy-up |
| Ctrl-B, j | copy-down |
| Ctrl-B, q | copy-exit |
| Ctrl-B, Ctrl-B | one literal Ctrl-B input byte |
| Ctrl-B, unknown key | original Ctrl-B plus key forwarded as input |

These are smux defaults. Prefixed k/j/q copy controls and forwarding unknown
bindings differ from exact tmux default key behavior. No configurable key table
or clipboard integration is claimed. Plain copy-mode navigation remains a
controller responsibility; this prefix-only decoder emits its bytes as input.

1. Forward ordinary Unicode, CR, Ctrl-C and an arrow escape sequence in one
   exact input action.
2. Read Ctrl-B separately from d. The first chunk retains a pending prefix;
   the second emits detach and clears it.
3. Read shell text followed by a trailing prefix, then a split binding and
   more text. Earlier input, split and later input keep their order.
4. Decode percent and double quote into the correct split directions.
5. Decode new window, next window, next pane, cycle layout and copy mode in
   order, with no invented command payloads.
6. Decode doubled Ctrl-B inside shell text as one literal Ctrl-B.
7. Forward an unknown binding, including its original prefix.
8. Preserve an unfinished prefix across an empty text chunk.
9. Complete a binding without mutating the prior prefix state value.
10. Preserve Unicode text across chunks, including an unknown Unicode binding.
11. Emit prefixed copy navigation and exit actions without claiming clipboard
    or copy-state changes.
12. Leave plain q, arrow, page and Escape bytes for the controller to interpret.
13. Decode three consecutive Ctrl-B bytes into a literal prefix and a pending
    prefix; a subsequent d completes detach.
14. Split actual UTF-8 byte sequences inside CJK and emoji scalars using the
    canonical raw-copy text boundary. Forward each fragment exactly; their
    concatenation reconstructs the original text.
15. Split an unknown prefixed emoji binding inside its scalar. Preserve both
    prefix and all Unicode bytes without replacement.

The decoder matches ASCII binding bytes without scalar decoding. Its raw-copy
fragment cases establish pure byte/state behavior only; the native console
facade supplies complete UTF-8 and the remote wire rejects invalid UTF-8. These
tests do not admit malformed native input or change either contract. They do not
prove console input mode, real key delivery, remote dispatch, shell focus,
rendering, copy history navigation or terminal restoration. Those require
controller and live-host evidence.

Required after runtime admission:

```text
<admitted-runtime> test test/03_system/tools/smux_client_input_spec.spl --native-backend=llvm --assert-ran --keep-artifacts
<admitted-runtime> spipe-docgen test/03_system/tools/smux_client_input_spec.spl --output doc/06_spec --no-index
<admitted-runtime> sspec-maintain scan test/03_system/tools/smux_client_input_spec.spl
```

Record exact runtime identity, case counts, exit status and artifacts. Require
complete generated documentation with zero stubs before accepting this manual.
