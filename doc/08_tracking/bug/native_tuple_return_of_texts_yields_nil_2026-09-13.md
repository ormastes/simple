# A `(text, text)` tuple return reaches the caller as `nil` in a stage-2 native binary (2026-09-13)

Status: OPEN. Worked around in the linker wrapper; the compiler defect is not fixed.

## What was observed

macOS Stage 2 sanity, lane
`bootstrap-from-scratch.sh --stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
worktree `agent-a0c7fd5436b74f37f`, 2026-09-13 00:06-00:16 local. Stage 2 built clean
(871 compiled, 0 failed, 135785 KB, linked `via clang++`), and the hello-world smoke link
failed with:

```
error: in-process native-build: LLVM native linking failed: Linking failed: nil
```

The producing code at that moment was
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`:

```
fn darwin_resolve_link_tool_report(command: text) -> (text, text):
    ...
    ("", tried)

pub fn darwin_link_tool_unresolved_error(command: text) -> text:
    val (_, tried) = darwin_resolve_link_tool_report(command)
    ...
    "darwin-link-tool-unresolved: command=" + command + " tried=[" + tried + "] PATH=" + path_value
```

`darwin_link_tool_unresolved_error` is declared `-> text` and its last expression is a
concatenation of non-nil texts, so it cannot legitimately produce `nil`. The identical
code returns the full message under the interpreter: the spec
`test/01_unit/compiler/native/darwin_link_tool_resolution_spec.spl` ran 7/7 green on the
Rust seed and printed the message verbatim. Only the NATIVE stage-2 binary produced `nil`.

## Why it matters beyond cosmetics

The whole point of that function was to carry a diagnostic trail out of a failing link.
The defect silently replaced the diagnosis with `nil`, i.e. it destroyed exactly the
evidence the change existed to produce, while leaving the failure itself intact. A
message-carrying return value that a backend can blank is not a reliable diagnostic
channel.

## Suspected shape

A tuple of two `text` values returned across a function boundary and destructured with
`val (a, b) = f(...)`. Not isolated further: the reproduction costs a ~25 minute Stage 2
build, and the workaround removed the need. Adjacent unknowns, none checked:
whether one element or the whole tuple is nil; whether arity, element type, or the
discard pattern `_` matters; whether the interpreter/seed path differs from native
because of tuple boxing.

## Workaround in place

`native_linking.spl` no longer returns a tuple anywhere on the darwin link-tool path.
`darwin_resolve_link_tool` returns a plain `text` ("" on failure) and
`darwin_link_tool_trail` builds the diagnostic separately, also as a plain `text`.
`darwin_link_tool_unresolved_error` additionally `print`s the message, because a
returned string is only as trustworthy as the machinery carrying it.

## Unblock condition

A minimal native-backend reproduction (two-element `text` tuple returned and
destructured, built with `native-build`, asserted non-nil), then a fix in the tuple
lowering. Until then: do not return tuples from functions on the native link path.

## Related

- `doc/10_metrics/infra/macos_bootstrap_chain_2026-09-12.md` (runs 1-6)
- PR #690 (the change that exposed this)
