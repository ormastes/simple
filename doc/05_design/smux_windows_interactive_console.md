# Native Windows interactive console

Status: authored implementation and fixtures; native execution pending.

`std.sys.terminal_console` is the single app-facing console capability. The
ordinary runtime composition returns explicit unsupported errors. Selecting
`src/providers/windows_native/lib` before `src/lib` binds the same interface
to `std.nogc_sync_mut.io.windows_console_owner`; app code does not inspect OS.

| Capability | Contract |
|---|---|
| open | `Result<i64,text>`, one exclusive console lease |
| read | `Result<text,text>`, nonblocking, max 1..65536 complete UTF8 bytes |
| size | `Result<[i64],text>`, actual window `[columns, rows]` |
| write | `Result<bool,text>`, bounded to 65536 UTF8 bytes |
| close | Invalidates read/write immediately; retries the same retained token |
| cleanup | Retries an unpublished failed-open restoration; does not close a live lease |
| clipboard_write | Explicit user action, bounded Unicode clipboard replacement |

Open duplicates actual standard input/output handles without inheritance.
GetConsoleMode rejects redirected streams. Before mutation, the owner saves
both exact modes. Raw input disables processed, line, echo, mouse, QuickEdit,
and VT input, and enables extended/window flags. Disabling processed input
allows Ctrl-C to reach the application as byte three. Output enables processed
and VT output plus DISABLE_NEWLINE_AUTO_RETURN to defer the bottom-right wrap
until a following printable character. Open enters the alternate screen and
hides the cursor.

One single-threaded owner reads input. GetNumberOfConsoleInputEvents precedes
ReadConsoleInputW, which requests at most 32 already available records. Another
consumer must not concurrently drain that console. INPUT_RECORD is 20 bytes:
event type0, keydown4, repeat8, virtual key10, Unicode WCHAR14, controls16.
KEY_EVENT keyup and modifier-only records do not emit data. The value codec
converts arrows, navigation, function keys and Shift-Tab to VT sequences;
Ctrl letters and Ctrl-Space preserve terminal control bytes. AltGr printable
text remains printable. A high UTF16 surrogate can survive OS reads, modifier
events and keyup; paired surrogate repeat counts remain compact counters.

The queue contains at most 64 small key records from one OS batch, rather
than expanding potentially 65535 repeats per key. Read emits complete key
sequences up to its byte limit. A caller that supplies less space than its
pending key requires receives empty text and must provide a larger limit;
the interactive client uses 4096. Output UTF16 conversion uses a retained
139264-byte arena and at most 16 WriteConsoleW calls per bounded write.
Write errors may follow a partial prefix; callers must not retry a complete
frame blindly. The write volume is bounded; no deadline guarantee is claimed
for the Windows console output API itself.

Close attempts alternate-screen exit, cursor visibility and color reset, then
attempts BOTH original mode restorations even when another cleanup step fails.
A retry re-enables VT before reattempting an incomplete alternate-screen exit,
then restores the exact original mode again. Failed native releases keep their
original owned handles/arena. Only successful mode/screen restoration permits
duplicate-handle release. Logical leases never reuse a slot, with a lifetime
bound of 100000. There is one active or privately retained restoring lease.
The client must retry close/cleanup for a finite deadline and report failure
if restoration remains incomplete; a single false return proves no restoration.

Clipboard is a separate native owner. It validates full Unicode, rejects NUL
and requests above 1MiB, and copies into GMEM_MOVEABLE|GMEM_ZEROINIT storage.
The console-associated HWND supplies clipboard ownership; NULL is rejected.
GlobalUnlock completion is disambiguated through GetLastError. Only a successful
SetClipboardData(CF_UNICODETEXT) transfers ownership to Windows; untransferred
storage is retained until successful release. CloseClipboard and failed frees
remain retriable. Console close/cleanup also attempts clipboard cleanup.
Clipboard replacement occurs solely when the user explicitly selects copy;
opening, reading, drawing and running the default fixture never modify it.

User32 is already named in the Windows platform/default MSVC and native-all
link support. Narrow nativecore builtin link lists do not themselves name it.
Actual product link receipts must prove user32 resolution; this source design
does not claim the current producer selected those defaults. No compiler or
frozen bootstrap source was modified for this interface.

Qualification artifacts:

- `test/01_unit/lib/io/windows_console_codec_spec.spl`: 12 value scenarios.
- `test/fixtures/compiler_entrypoint/windows_console_owner/main.spl`: run
  inside an isolated ConPTY under an external watchdog. It injects deterministic
  input records, measures an empty poll, checks Unicode/VT/control events,
  checks child-visible dimensions, a top-row sentinel after bottom-right paint
  (no unintended viewport scroll), and exact original mode restoration, and
  requires the actual child exit status. It clears only that isolated console's
  input queue. A piped direct launch fails instead of silently skipping.
- Positive system clipboard copy remains an explicit manual user-action gate;
  the automated fixture deliberately preserves the user's system clipboard.

The external host must bound startup/total execution (recommended 15 seconds),
continuously drain ConPTY output, require the computed fixture PASS marker and
exit status zero through the retained child handle, then require terminal
JobObject cleanup. The host must terminate/reap its owned process tree on any
timeout. In-process timing assertions alone do not bound a blocked native call.
Compile and run independently with admitted Phase2 and Phase3 producers.

References: [console modes](https://learn.microsoft.com/en-us/windows/console/setconsolemode),
[input event count](https://learn.microsoft.com/en-us/windows/console/getnumberofconsoleinputevents),
[KEY_EVENT_RECORD](https://learn.microsoft.com/en-us/windows/console/key-event-record-str),
[clipboard ownership](https://learn.microsoft.com/en-us/windows/win32/api/winuser/nf-winuser-setclipboarddata),
[console-associated HWND](https://learn.microsoft.com/en-us/windows/console/getconsolewindow).
