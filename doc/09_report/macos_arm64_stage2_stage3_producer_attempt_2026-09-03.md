# macOS arm64 Stage2→Stage3 Producer Attempt — 2026-09-03

## Verdict

**BLOCKED before Stage2; no artifact or receipt was produced.**

The documented production entrypoint was invoked exactly once with the
hash-bound admitted pure-Simple runtime and `--stop-after-stage3`. It exited 64
at the planner-admission boundary because no producer-authenticated Stage2
parent exists from which the required Stage3 planner receipt can be derived.

## Admitted runtime

- Path: `/Users/ormastes/simple/bin/release/macos-arm64/simple`
- SHA-256: `277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767`
- Identity: `Simple v1.0.0-rc.1`
- Admission: `scripts/lib/runtime-provenance/277f8ac9e14ae266ce380a5890d434ce27b47cee9378e2b337cbcc8cd4086767.env`

The Rust seed and the misleading `aarch64-apple-darwin` artifact were not used.
No standalone binary was copied into Stage2 and no receipt was synthesized.

## Production invocation

```text
SIMPLE_BUILD_COMPILER=<admitted-runtime> SIMPLE_BINARY=<admitted-runtime> \
scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --stop-after-stage3 \
  --output=build/bootstrap/arm64-stage2-stage3-attempt-20260903 \
  --jobs=1 --no-mcp
```

The authoritative stderr was:

```text
bootstrap-policy-error: reason-receipt-required; run 'simple run src/app/build/bootstrap_receipt_main.spl --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path> --parent-compiler-sha256=<hex64> --runtime-snapshot-sha256=<hex64> --planner-source-closure-sha256=<hex64> --planner-sha256=<hex64>'
```

## Why this is not repaired locally

`produce-bootstrap-planner-admission-v2.shs` intentionally requires an existing
Stage2 compiler plus its producer-created sanity, provenance, and admission
receipts. The only receipt-free Stage2 path currently requires
`--full-bootstrap`, whose authority is the Rust seed. Permitting an admitted
release binary to impersonate Stage2, copying it into Stage2, or manufacturing
the missing parent receipts would break the non-circular trust model and violate
the requested constraints.

Therefore this is an unavailable prerequisite, not a safe narrow script fix.
The next legitimate action is a producer-authorized Stage2 trust-root run on a
lane where use of the Rust bootstrap root is allowed, followed by planner receipt
production and the one-shot Stage3 resume. Under the no-seed constraint, the
Stage2→Stage3 chain cannot begin from the currently retained evidence.

## Retained evidence

Exact logs, environment identity, exit status, and hashes are retained under
`build/review/arm64-stage2-stage3-attempt-20260903/`.
