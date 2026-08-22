# SimpleOS WM IPC protocol: 8 status/event symbols imported by live code were never implemented

**Status:** RESOLVED in source (2026-08-22); runtime execution remains subject
to the repository's admitted self-hosted-runtime gate. The common protocol now
defines every originally missing name and strict byte codecs. The create reply
remains exactly `status(i32 LE) | window_id(u64 LE)` (12 bytes). The focus body
remains exactly `window_id(u64 LE) | focused(u8)` (9 bytes) after the existing
`COMP_FOCUS_CHANGED` method word. The WM service encodes through those common
owners, and WindowClient decodes create replies through the same owner.
**Found:** 2026-07-28 (dangling-reference triage, `src/os/**` scope)
**Area:** `src/lib/common/window_protocol/window_protocol.spl`,
`src/os/services/wm/`, `src/os/userlib/_Window/`, `src/os/desktop/`
**Severity:** high — live WM IPC code paths dereference symbols that exist in no
source file. Kernel-adjacent userland (window manager wire protocol).

## Finding

`src/lib/common/window_protocol/window_protocol.spl` (88 lines) declares only:

```
val WM_EVENT_CLOSE
class WmInputEvent
struct WmCreateRequest
struct WmCloseRequest
struct WmResizeRequest
struct WmMoveRequest
```

Six of the ~14 names its consumers import. The following eight are **declared in
no `src/**/*.spl` file at all**:

| Missing symbol | Kind implied by use site |
|---|---|
| `WM_STATUS_OK` | status constant with a `.value` field |
| `WM_STATUS_ERROR` | status constant |
| `WM_STATUS_NO_SPACE` | status constant |
| `WmStatus` | the status type itself |
| `WmCreateResponse` | response struct |
| `WmFocusEvent` | event struct |
| `WM_EVENT_FOCUS` | event tag |
| `WM_EVENT_RESIZE` | event tag |
| `wm_input_event` | constructor fn |
| `wm_focus_event` | constructor fn |

## This is not a dead import — the symbols are dereferenced

```
src/os/services/wm/wm_codec.spl:19:        _push_i32(buf, WM_STATUS_OK.value)
src/os/userlib/_Window/client_methods.spl:196:  if status == WM_STATUS_OK.value and wid > 0:
```

Both sites read a `.value` field off `WM_STATUS_OK`, which implies the intended
shape is a struct/enum constant, not a bare `val`. The WM reply codec cannot
encode a status word and the client cannot decode one.

## Referencing sites (32 checker findings)

```
src/os/desktop/shell.spl:29                    WM_STATUS_ERROR
src/os/services/wm/wm_codec.spl:8              WM_STATUS_OK, WmStatus
src/os/services/wm/wm_service.spl:32           WmCreateResponse, WmFocusEvent, WM_EVENT_FOCUS,
                                               WM_STATUS_OK, WM_STATUS_ERROR, WM_STATUS_NO_SPACE,
                                               wm_input_event, wm_focus_event
src/os/userlib/_Window/client.spl:32           WmCreateResponse, WmFocusEvent, WM_EVENT_FOCUS,
                                               WM_EVENT_RESIZE, WM_STATUS_OK, WM_STATUS_ERROR,
                                               wm_input_event
src/os/userlib/_Window/client_methods.spl:32   (same set as client.spl)
src/os/userlib/_Window/ipc_helpers.spl:32      (same set as client.spl)
```

## Git evidence — NEVER-EXISTED, not wrongly deleted

`window_protocol.spl` has been **88 lines in every revision of its history**.
Sampling the 12 most recent commits that touch it (`--follow`), the count of
`WM_STATUS_OK` occurrences in the blob is `0` at every single one:

```
37cda4befdc lines=88  WM_STATUS_OK=0   fix(vcs): restore main from pushed jj conflict tree
752425d3fcc lines=88  WM_STATUS_OK=0   resolve: merge engine2d webgpu backend conflicts after rebase
3f577c312de lines=88  WM_STATUS_OK=0   revert(sync): restore sane tree ...
7c30ce49d04 lines=88  WM_STATUS_OK=0   wip: working-copy snapshot (hourly sync)
270ff899b9b lines=88  WM_STATUS_OK=0   test(traits): add cross-module trait default dispatch repro
369a3725bbe lines=88  WM_STATUS_OK=0   revert: restore 13,174 files mass-deleted by e3e22d19da
```

(The interleaved `lines=0` revisions are the known torn-working-copy /
jj-conflict-tree commits, each immediately reverted back to the same 88-line
blob — they are churn, not a truncation that lost these symbols.)

No definition-shaped occurrence of any of the eight names exists anywhere in
history under `src/`. **Classification: NEVER-EXISTED — a real capability gap.**

## Why this is not fixed here

Implementing it means choosing the WM IPC **wire encoding** (status word width,
event tag representation, `WmCreateResponse` field order) that
`wm_codec.spl`/`client_methods.spl` must agree on byte-for-byte, and SimpleOS
runs on real hardware. Guessing an encoding would change kernel-adjacent
behaviour with no test to catch a mismatch. Needs an owner who can fix the
protocol definition against the codec.

## Re-verification (2026-08-10)

`window_protocol.spl` grew from 88 to 107 lines since this doc was filed, but
the added lines are unrelated (`WM_INPUT_TEXT_MAX_BYTES` and other
`WmInputEvent` internals) — all 8 missing symbols
(`WM_STATUS_OK`/`WM_STATUS_ERROR`/`WM_STATUS_NO_SPACE`/`WmStatus`/
`WmCreateResponse`/`WmFocusEvent`/`WM_EVENT_FOCUS`/`WM_EVENT_RESIZE`/
`wm_input_event`/`wm_focus_event`) are still declared nowhere in the file; the
declared-symbol set (`WM_EVENT_CLOSE`, `WmInputEvent`,
`WmCreateRequest`/`WmCloseRequest`/`WmResizeRequest`/`WmMoveRequest`) is
identical to what this doc originally found. No fix was attempted in that
2026-08-10 pass; that historical conclusion is superseded below.

## Resolution evidence (2026-08-22)

- `window_protocol_wire_spec.spl` checks byte literals, valid round trips,
  truncated/trailing payloads, unknown status words, contradictory
  status/window pairs, invalid focus booleans, zero IDs, and the three legacy
  event-tag constructors with real assertions.
- Both codecs are O(1), operate on fixed 12-byte/9-byte records, and use no
  text or unbounded payload allocation.
- No C or Rust provider was added; this remains a Pure-Simple common contract.
