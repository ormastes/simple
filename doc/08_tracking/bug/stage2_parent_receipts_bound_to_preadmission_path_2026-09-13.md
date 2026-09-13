# Site 15: Stage 2 IS admitted, then the parent receipts refuse to publish — silently

- **Status:** FIXED (2026-09-13) — the caller named the pre-admission path.
- **Lane:** macOS `--stop-after-stage2 --full-bootstrap --mode=dynload --jobs=half`,
  worktree `agent-aee4c61a47998a6a9`, run 28 (the run carrying the site-13 and
  site-14 fixes).
- **Severity:** the Stage-2 blocker that succeeds site 14. Not caused by it —
  masked by it: run 27 was refused at the admission receipt, one step earlier.

## The verdict

```
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
error: could not publish producer-bound Stage 2 parent receipts
```

No `stage2-sanity-error:` line this time — **site 14 is cleared**, the sanity
evidence verified, and the immutable admission receipt WAS published:

```
$ ls .../stage3/aarch64-apple-darwin/stage2-admitted/
-r--------  admission.env      (2647 B)
-r-x------  simple             (139,352,344 B)
```

The failing step is inside the `else` branch that runs only AFTER admission
succeeds (`bootstrap-from-scratch.sh:3206`): the producer-bound **parent**
receipts, which seed the next run's trust root.

## Measured cause — the caller names a different file than the receipt does

`publish-stage2-parent-receipts.shs` asserts, under `set -eu` with bare `[ ]`
(so a failure exits 1 with no message):

```sh
[ "$(field candidate_path)" = "$candidate" ]
```

Measured on the real artifacts, three of four path fields match and one does not:

| field | receipt says | caller passed |
|---|---|---|
| `candidate_path` | `…/stage3/<triple>/stage2-admitted/simple` | `…/stage2/<triple>/simple` |
| `source_snapshot_path` | match | match |
| `runtime_snapshot_path` | match | match |
| `tool_authority_path` | match | match |

`bootstrap-from-scratch.sh:3212` passed `"$(absolute_path "${stage2_bin}")"` —
the mutable build output — while the admission receipt records the immutable
admitted copy. The producer is right and the caller is wrong: the parent
receipts must bind to the artifact the admission receipt admitted.

The two files are byte-identical (`cp -p` at `:3167`, sha-verified at `:3172`):

```
c85d2aa186e45c8a86ca1081265610ae91c9c31edafb6c3497b1f2bc206beef2  …/stage2/<triple>/simple
c85d2aa186e45c8a86ca1081265610ae91c9c31edafb6c3497b1f2bc206beef2  …/stage2-admitted/simple
```

so the fix changes which path is NAMED, not which bytes are bound. Every sha
assertion in the producer is unaffected and still enforced.

## Why no test caught it

`test/01_unit/scripts/stage2_parent_receipt_producer_test.shs` exercises the
PRODUCER against a fixture it builds itself, and that fixture always writes
`candidate_path=$candidate` — i.e. it can never disagree with the argument. The
defect is in the CALLER, which no test invokes. The gap is real and is recorded
here rather than papered over; closing it needs a caller-level fixture, not a
change to the producer.

## Fix

`bootstrap-from-scratch.sh:3212` now passes
`"$(absolute_path "${stage2_admitted_bin}")"`.
