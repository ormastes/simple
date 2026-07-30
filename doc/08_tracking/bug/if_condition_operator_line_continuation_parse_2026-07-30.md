# Operator line-continuation fails inside an `if` condition (parses fine in a binding)

**Status:** OPEN, unfixed. **Found:** 2026-07-30, while running
`scripts/check/check-linux-hosted-wm-live-window-evidence.shs`.
**Severity:** a file at origin tip does not parse with the current
toolchain, so every consumer of it fails at discovery.

## Minimal repro (PROVED)

```simple
# FAILS: continuation after a comparison operator in an `if` condition
fn f(a: i64, b: i64) -> bool:
    if a >
       b:
        return true
    false
```
```
Unexpected token: expected expression, found Newline
```

```simple
# PARSES: the same continuation style in a `val` binding
fn g(a: i64, b: i64) -> i64:
    val x = a +
       b
    x
```

So operator line-continuation **is** supported in expression/binding
position but **not** inside an `if` condition. This is the "short, safe
grammar form fails" case CLAUDE.md says to record rather than silently
normalize — the workaround (join the condition onto one line) should not
be applied without a decision, because the grammar is inconsistent
between the two positions.

## Real-world impact (PROVED)

`src/lib/common/web/browser_renderer_protocol.spl:559` uses the failing
form:

```simple
    if payload_bytes.len().to_i64() >
       BROWSER_RENDERER_MAX_PAYLOAD_BYTES - capability_bytes:
```

Introduced by `ba0ce4e3c06` *"feat(web): add SBR2 command capability
codec"* (2026-07-30) — `git log -L 558,560:` on that file.

The file therefore **fails to parse at origin tip** with:

- the newest deployed seed
  (`bin/release/x86_64-unknown-linux-gnu/simple`, 154,094,616 bytes,
  sha256 `79ca755d…`, LLVM-linked, deployed 2026-07-30 09:08), and
- the newest self-hosted binary on this host
  (`build/redeploy_out/simple_stage2`, 2026-07-28).

Both fail with the same `expected expression, found Newline`, so this is
**NOT** a stale-binary problem — it is a genuine grammar/source
incompatibility at tip.

## How it surfaced

It is the current blocker of the host-WM evidence gate: with walls 1-7
satisfied, `check-linux-hosted-wm-live-window-evidence.shs` now fails at
`reason=production-native-build-failed`, whose
`native-build.log` reads:

```
Build failed: failed to parse .../src/lib/common/web/browser_renderer_protocol.spl
at 559:38 during discovery: Unexpected token: expected expression, found Newline
```

## Fix options (not applied here — needs a decision)

1. **Extend the parser** so an `if` condition accepts continuation after a
   trailing binary operator, matching binding position. Preferred: keeps
   the grammar consistent and needs no source churn.
2. **Normalize the source** at `browser_renderer_protocol.spl:559` onto
   one line. Cheap and unblocks the gate immediately, but encodes the
   grammar inconsistency rather than fixing it, and CLAUDE.md explicitly
   warns against silently normalizing such workarounds.

Not chased in this pass (gate work was scoped to characterize, not fix).
