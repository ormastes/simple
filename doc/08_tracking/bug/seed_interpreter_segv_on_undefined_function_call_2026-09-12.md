# `simple run` SEGVs on a call to an undefined function (the `compile` lane diagnoses it)

Date: 2026-09-12. Host: Windows 11 (Git Bash). Binary: `bin/simple.exe`
(Rust bootstrap seed, built 2026-09-02, 16,347,136 bytes).
Status: OPEN. Lane: **interpreter/JIT (`run`) only** — see "Phase-2 applicability".
Found while diagnosing: `t32_mcp_server` exiting with rc=139 and no diagnostic.

## Symptom

Calling a function name that resolves to nothing terminates the process with
SIGSEGV (rc=139) and **prints nothing at all** — no error, no location, no
identifier name. The same program compiled with `simple compile` is rejected
cleanly, so the semantic check exists; the `run` lane does not consult it.

## Minimal reproduction (rc read into a variable, never through a pipe)

`a.spl`, two lines, no imports:

```
fn main():
    no_such_fn()
```

```
$ timeout 60 ./bin/simple.exe run a.spl > out 2> err; echo "rc=$?"
Segmentation fault
rc=139
# out: empty.  err: only the "bootstrap seed only" banner.
```

## Discriminating probes (same binary, same session)

| probe | body | rc | diagnostic |
|---|---|---|---|
| undefined **function**, no args | `no_such_fn()` | **139** | none |
| undefined **function**, with arg + binding | `val x = no_such_fn("a")` | **139** | none |
| undefined **variable** | `print(no_such_var)` | 1 | `[CODEGEN BODY] Function 'main' body compilation failed: GlobalLoad: unresolved identifier 'no_such_var' (not a global, function, const-data name, or import)` then `[CODEGEN-STUB-FALLBACK]` |
| undeclared-backing **extern** | `extern fn stderr_write(data: text) -> i64` + call | 0 | `interpreter_sffi.rs:797 rt_interp_call: function not found: stderr_write`, call returns nil (the separately tracked "unregistered extern silent nil" class) |
| control | `print("ok")` | 0 | prints `ok` |
| **same file via `compile`** | `no_such_fn()` | **1** | `error: compile failed (a.spl): semantic: Undefined("undefined identifier: no_such_fn")` |

So: an unresolved *load* is diagnosed on the run lane, an unresolved *call* is
not — it is lowered to a call through a null target and faults. The AOT lane
catches the identical program in the semantic phase.

## Why it matters (the incident that surfaced it)

`examples/10_tooling/trace32_tools/t32_mcp/protocol.spl` calls plain-name JSON
helpers (`js`, `jp`, `jo1..jo4`, `Q`, `LB`, `RB`, `SB_L`, `SB_R`,
`escape_json`, `jsonrpc_result`, `jsonrpc_error`, `strip_last`) that
`json_helpers.spl` did not define.

History, measured with `git show <rev>:<path> | grep -c '^fn js('`:

| rev | `fn js(` in `t32_mcp/json_helpers.spl` |
|---|---|
| `6855c8906e1~1` (pre-clobber) | **1** |
| `6855c8906e1` (stale-snapshot clobber) | file absent |
| `5f1403b7680` (PR #583 restore) | **0** — file back, plain names still missing |

So PR #583 restored the file from a snapshot that predates or omits the
plain-name definitions; the `t32_*` spellings came back and the short aliases
did not. That is a partial restore, not a second deletion.

Isolated to that one file, measured: with only `json_helpers.spl` swapped back
to the `5f1403b7680` content and every other file left as-is,

```
$ timeout 120 ./bin/simple.exe run examples/10_tooling/trace32_tools/t32_mcp/main.spl < init.json > out 2> err; echo "rc=$?"
Segmentation fault
rc=139        # out: 0 bytes
```

and with the file restored, the same command answers `initialize` +
`tools/list` at rc=0 with a 16,311-byte response. One file, one silence.

The second silence was the wrapper: `bin/release/x86_64-pc-windows-msvc/t32_mcp_server.cmd`
line 15 ended in `2>nul`, so even the seed's own banner was discarded. A crash
that says nothing, behind a wrapper that shows nothing.


A one-word typo in any `.spl` reaching the interpreter costs a bare SIGSEGV.

## Phase-2 applicability (Stage-2 self-hosted compile path)

**Interpreter-only.** Measured, not inferred: the same source through
`bin/simple.exe compile` fails with a proper `semantic: Undefined("undefined
identifier: no_such_fn")` at rc=1 (row 6 above). The resolver that phase 2
depends on has the check; only the `run` lane's lowering skips it and emits a
call to a null target. So a compiled Stage-2 ARTIFACT cannot carry this fault. It is not fully out of phase 2's way, though: the native-build worker is `bin/simple.exe` INTERPRETING the pure-Simple pipeline (`native-build worker exited with code 1.  interpreter: bin/simple.exe`), so an unresolved call in compiler or stdlib sources on that lane would SEGV the worker instead of naming the identifier. The adjacent
call-to-zero class in native codegen is a different, already-tracked defect —
`stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11.md`.

## Suggested fix

On the `run` lane, route an unresolved *call* target through the same
`GlobalLoad: unresolved identifier` diagnostic the load path already produces
(rather than emitting the call), so the failure is a rc=1 message naming the
identifier instead of a silent SIGSEGV.

## Runnable check

`scripts/check/check-t32-mcp-server-runnable.shs` — fail-closed. Asserts the
MCP handshake + `tools/list` round-trip returns rc=0 (this exact case was
rc=139), and that no generated `t32_mcp_server.cmd` swallows stderr with
`2>nul`. `--selftest` is fatal and includes the two-line reproducer above,
which must SEGV for the gate's premise to hold.
