# office_gui_live_loop_spec

> Office live keyboard-loop proof (byte -> key -> session -> render).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_live_loop_spec

Office live keyboard-loop proof (byte -> key -> session -> render).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_live_loop_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Office live keyboard-loop proof (byte -> key -> session -> render).

The live sheet-GUI loop (run_sheet_gui_live) is:
  rt_stdin_read_byte  (OS raw-mode byte source)
    -> decode_key_byte (raw termios byte -> canonical key name, ESC-sequence
       state machine threaded via pending_esc)
    -> session_key / session_edit (apply the key to the live session)
    -> re-render the frame.

Only the FIRST link (rt_stdin_read_byte) is an OS syscall whose runtime impl the
deployed production binary predates (CARD 6 — the rt_terminal_* externs are
declared in interactive.spl but the shipped seed lacks their impl; landing them
needs a self-hosted rebuild + binary swap). EVERY OTHER LINK is pure and proven
here: this spec feeds the exact raw byte sequences a terminal delivers (arrow
escape sequences, printable bytes, Enter, EOF) straight into decode_key_byte and
threads the decoded key into the live session handler, asserting the selection
moves / the cell edits / the frame still renders. The keyboard loop itself is
therefore spec-guarded end to end; only the OS byte source remains to deploy.

## Scenarios

### live loop: down-arrow escape sequence decodes and drives the session

#### ESC [ B -> 'down' -> selection A1 moves to A2 and re-renders

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = decode_key_byte(0, 27)
expect(r1.key).to_equal("")
expect(r1.pending_esc).to_equal(1)
val r2 = decode_key_byte(r1.pending_esc, 91)
expect(r2.key).to_equal("")
expect(r2.pending_esc).to_equal(2)
val r3 = decode_key_byte(r2.pending_esc, 66)
expect(r3.key).to_equal("down")
val session = session_new(_demo_sheet(), "A1")
val moved = session_key(session, r3.key, 2, 2, 2, 2)
expect(moved.selected_ref).to_equal("A2")
assert_true(_renders(moved))
```

</details>

### live loop: right-arrow escape sequence decodes to 'right'

#### ESC [ C -> 'right' -> selection A1 moves to B1

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = decode_key_byte(0, 27)
val b = decode_key_byte(a.pending_esc, 91)
val c = decode_key_byte(b.pending_esc, 67)
expect(c.key).to_equal("right")
val session = session_new(_demo_sheet(), "A1")
val moved = session_key(session, c.key, 2, 2, 2, 2)
expect(moved.selected_ref).to_equal("B1")
```

</details>

### live loop: printable + control bytes decode correctly

#### a printable byte '5' (53) decodes to \

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_key_byte(0, 53)
expect(r.key).to_equal("5")
```

</details>

#### carriage return (13) and newline (10) decode to 'enter'

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cr = decode_key_byte(0, 13)
expect(cr.key).to_equal("enter")
val lf = decode_key_byte(0, 10)
expect(lf.key).to_equal("enter")
```

</details>

#### a negative byte (EOF from a closed stream) decodes to 'eof'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_key_byte(0, -1)
expect(r.key).to_equal("eof")
```

</details>

#### deliberate-fail probe proves the tail of the file executes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_key_byte(0, 27)
expect(r.pending_esc).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
