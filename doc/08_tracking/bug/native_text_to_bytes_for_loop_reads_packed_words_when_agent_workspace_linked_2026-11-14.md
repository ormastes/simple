# Native: `for b in text_to_bytes(s)` yields packed 8-byte words once `app.llm_caret.agent_workspace` is in the unit

Status: open
Severity: P1 (native-only wrong result, silent)
Found: 2026-11-14, lane `work/caret-native-knob-20261114`
Seed: `/c/dev/wt/seed-tip/simple.exe`, build-commit `97728d94d5f11890bac2e0a5e8d41ce65139047b`
Host: Windows 11, llvm-mingw 20260922 UCRT, `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1`

## Symptom

Native `llm_caret.exe workspace <id> attach agent-1` exits 1 with
`error invalid_name agent-1`. The interpreter accepts the same name.
`_valid_name` (`src/app/llm_caret/agent_workspace.spl:403`) iterates
`text_to_bytes(name)` and sees garbage instead of byte values, so every name is
rejected on the smux backend.

Visible in the suite as the native-mode failure of
`test/03_system/app/llm_caret/workspace_cli_system_spec.spl`
("attaches three agents, isolates their worktrees, broadcasts, and tears down"):

```
expected 1 to equal 0
expected error invalid_name agent-1
 to contain window cli-team:agent-1
```

Run with `LLM_CARET_NATIVE_BIN=<native llm_caret.exe>`:
`Results: 4 total, 3 passed, 1 failed`. Interpreted: `4 total, 4 passed, 0 failed`.

## Minimal repro

`probe.spl`:

```simple
use std.common.string_core.{text_to_bytes}
use app.llm_caret.agent_workspace.{workspace_backend, window_open, agent_workspace}

fn main() -> i64:
    for b in text_to_bytes("a-1"):
        print "byte=" + b.to_i64().to_text()
    print "backend=" + workspace_backend()
    val r = window_open(agent_workspace("probe-x", ".", ""), "bad name!", ".", "")
    print "bad=" + r.status + " " + r.reason
    0
```

```
$SEED native-build probe.spl -o probe.exe --cache-dir build/nb/cache && ./probe.exe
```

Native output (462 modules compiled):

```
byte=3222881
byte=-9223366535643127486
byte=0
```

`3222881 == 0x312D61`, i.e. the three bytes `a - 1` read as ONE little-endian
8-byte word: the loop makes 3 iterations (length is right) but loads each
element with an 8-byte stride from a packed `[u8]` buffer.

Control 1 - same file without the `agent_workspace` import (3 modules compiled),
native: `byte=97 / byte=45 / byte=49` (correct).
Control 2 - either file under `$SEED run`: `97 / 45 / 49` (correct).

So the defect is not in `text_to_bytes` itself; it depends on what else is
co-compiled. Not yet isolated which module flips it.

## Leads (unverified)

- Two public `text_to_bytes(s: text) -> [u8]` definitions exist:
  `src/lib/common/text_bytes.spl:31` (re-exported by
  `src/lib/common/string_core.spl:496`, returns the packed `rt_text_to_bytes`
  array) and `src/lib/common/base_encoding.spl:85` (builds `var out: [u8] = []`).
  If the large unit resolves the call to one definition but types the loop
  element from the other (or loses the `[u8]` element type on a `$dupN`
  variant), the 8-byte stride follows.
- Possibly related: `core_string_bytes_word_slot_tag_mismatch_2026-10-05.md`,
  `byte_span_cross_module_misread_2026-07-19.md`.

## Unblock condition

The repro prints `97 / 45 / 49` natively, and
`workspace_cli_system_spec.spl` passes 4/4 with `LLM_CARET_NATIVE_BIN` set.
No caret-side workaround was applied.
