# `native-build` of a hello world fails in phase 3 with its diagnostics lost in transport

- **Filed:** 2026-09-02
- **Status:** OPEN
- **Severity:** P1 — the build fails AND destroys the evidence of why, so the
  failure cannot be triaged from its own output
- **Component:** seed `native-build` worker / diagnostic transport
- **Found by:** the bug-DB triage lane, while closing
  `export_use_wildcard_rejected_but_used_1719_times_2026-08-17.md`

## Symptom

On a seed built from `origin/main` `1b76db1d6c3` (aarch64-apple-darwin), the
two-line hello world from the record above:

```
$ printf 'fun main()\n  print("hi42")\n' > hw.spl
$ <fresh-seed> native-build hw.spl -o /tmp/hw.bin
...
[ERROR] phase 3 FAILED
[build] hir unknown/unknown step 2/6 +6208ms dt=77ms failed
[ERROR] phase 3 FAILED (diagnostics unreadable: error array did not survive transport)
error: native-build worker exited with code 1.
RC=1
```

Repeated three times as `error: native-build failed without diagnostics`.

## Why this is filed separately

It is the residual failure left after the `export use X.*` row was closed. That
row claimed the build was blocked by a rejected `export use` form; measurement
showed that diagnostic is now a WARNING (75 of them are printed and the
pipeline walks past all of them) and the build dies later, here. Leaving this
attached to that row would keep a fixed diagnostic looking live and hide a
distinct defect behind it.

## What makes it worse than an ordinary build failure

The message is explicit that the error array "did not survive transport": the
worker knows it failed and knows it cannot say why. Every downstream consumer —
a gate reading a verdict, a person reading a log — gets a build failure with no
cause. The phase and step are named (`hir`, step 2/6), so the transport, not
the detection, is the missing half.

## Not established

- Whether the underlying phase-3 error is itself a real defect or a
  configuration gap on this host.
- Whether the transport loss is specific to the worker path or also affects
  in-process builds.
- Whether other platforms reproduce; only aarch64-apple-darwin was measured.

## First thing to do

Make the worker fail LOUD before fixing whatever phase 3 is unhappy about — a
build that cannot report its own errors will hide the next defect too.
