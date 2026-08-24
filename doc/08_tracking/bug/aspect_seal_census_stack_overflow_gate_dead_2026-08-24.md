# Aspect-seal census stack-overflows — Phase 6 exit gate is dead, not green

**Date:** 2026-08-24
**Severity:** HIGH (a hardening exit gate reports ERROR, and its last recorded PASS is unreproducible)
**Status:** SUPERSEDED / already FIXED upstream — 2026-08-24

> **Superseded by** `doc/08_tracking/bug/seed_file_read_infinite_recursion_stack_overflow_2026-08-23.md`
> and the fix in commit `1ca19a1e31a` ("fix(stdlib): file_read aborted the
> process -- two forwarders closed into infinite mutual recursion").
>
> The diagnosis below — that the aspect-seal *census* or its aspect-parsing path
> was at fault — is **wrong**. The census and the parser are both fine. The real
> cause is a cross-module name collision: `file_read` has a second co-compiled
> definition at `src/lib/nogc_sync_mut/io/file_ops.spl:76` whose body is
> `read_file_text(path)`, so when resolution fell back to last-definition-wins,
> `io_runtime.read_file_text -> file_ops.file_read -> read_file_text -> …`
> recursed with no base case and aborted the process on the FIRST read of ANY
> file. Every script under `src/app/**` pulls `file_ops` in via
> `app/io/mod_stub.spl`, which is why it presented as "reading a file crashes,
> but only from `src/app`". The observation recorded below — that the census
> completes when no `--aspect` is passed — is still correct, and was the clue:
> without `--aspect`, nothing reads a file.
>
> The fix points `read_file`/`read_file_text` at `file_read_result`, whose name
> has exactly one definition in the tree. Verified on this tree at
> `origin/main` `ffc46d283524`: `sh scripts/check/check-aspect-seal.shs` →
> `PASS — 1 aspect(s) checked, unbound-required=0 late-activation=0
> post-weave-recheck=ran`. The Phase 6 gate is live again.
>
> Kept for the trail; do not act on the resume steps below.
**Plan section:** hardening plan Phase 6 (`doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`)

## Symptom

`sh scripts/check/check-aspect-seal.shs` exits **2**:

```
ERROR — nothing was checked (selftest failed: positive-fixture-produced-no-summary
  unbound-required-not-detected duplicate-binding-not-detected
  late-activation-not-detected unverified-signature-not-detected)
```

All five fixtures fail at once, which is the signature of the driver dying
rather than of five independent detection defects.

## Root cause (reproduced directly)

The census driver aborts on the currently deployed compiler:

```console
$ bin/simple run src/app/check/aspect_seal_census.spl --critical \
      --aspect test/fixtures/aspect_seal/audit_trace_clean.sdn
thread 'simple-main' (2121154) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

With no `--aspect` argument the same driver runs to completion
(`SUMMARY aspects=0 ... parse_fail=0`), so the fault is on the aspect-parsing
path, not in startup.

## Binary identity

```
bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple
60650360 bytes, 2026-08-23 04:47:05 UTC, sha256 f6521b60b67d3894…
--version: Rust bootstrap SEED warning banner present
```

The Phase 6 PASS recorded on 2026-08-21 was minted against artifact
`5d35debcec323548…` — a different binary. The fixtures themselves are
unchanged since the landing commit `1df56d314f5` (`test/fixtures/aspect_seal/`,
mtime 2026-08-21 06:33), so the change is on the compiler side.

## Why this matters beyond one gate

`check-aspect-seal` is a required Phase 9 release obligation
(`scripts/check/critical_release_required_receipts.txt`). Because the gate
ERRORs it mints no fresh receipt, so `check-critical-release-seal.shs` reports
the obligation as stale. That is the fail-closed behaviour working — but it
means the aspect half of §22.4 currently has **no executable evidence at all**,
and the plan text still describes it as landed and green.

## Not yet determined

- Whether the overflow is unbounded recursion in the census's own SDN walk or in
  the seed's parser/interpreter. Both are plausible; nothing here decides it.
- Whether a pure-Simple (non-seed) binary reproduces it. `bin/simple` is the
  Rust seed today, so the run above is seed evidence only.

## Resume

- **Owner:** Phase 6 aspect lane.
- **Prerequisite:** none for diagnosis; a pure-Simple redeploy for the parity half.
- **Command:** `bin/simple run src/app/check/aspect_seal_census.spl --critical --aspect test/fixtures/aspect_seal/audit_trace_clean.sdn`
- **Done when:** `sh scripts/check/check-aspect-seal.shs` exits 0 and
  `sh scripts/check/refresh-critical-release-receipts.shs --only check-aspect-seal`
  reports the obligation fresh.

## Update 2026-08-24 — does NOT reproduce on clean origin/main; the laundering half is FIXED

Two separate defects were conflated under this record. They are now separated.

### 1. The stack overflow does not reproduce on a clean tree

Measured in a fresh `git worktree` detached at `origin/main` (`d62957f017b`),
using the same deployed seed as the original report:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ sh scripts/check/check-aspect-seal.shs ; echo rc=$?
PASS — 1 aspect(s) checked, unbound-required=0 late-activation=0 post-weave-recheck=ran
rc=0
$ sh scripts/check/check-aspect-seal.shs --selftest ; echo rc=$?
PASS — 5 selftest fixture(s) checked, scanner detects all four rejection classes
rc=0
```

All five selftest fixtures pass, including the four rejection classes the
original report listed as undetected. The original
`ERROR — nothing was checked (selftest failed: positive-fixture-produced-no-summary
unbound-required-not-detected duplicate-binding-not-detected
late-activation-not-detected unverified-signature-not-detected)` was measured in
the SHARED worktree `/mnt/data/worktrees/simple-main`, which carries hundreds of
uncommitted modifications and runs well behind origin. This is the same
stale-worktree class that produced four phantom `check-engine-differential`
divergences the same day. NOT closed: the overflow may still be real against
that worktree's modified driver source, and this note is evidence about clean
origin/main only, not a refutation of the original observation.

### 2. The receipt laundering was real, is structural, and is fixed

Independent of the overflow, and the more dangerous half: **every** ERROR path
in `check-aspect-seal.shs` exited 2 without touching `build/evidence/`, so the
gate's PREVIOUS `PASS` receipt stayed on disk — still bound to the same artifact
and seal hash, still inside the freshness window — and
`check-critical-release-seal.shs` kept counting it. A dead gate laundered into
release evidence. Reproduced verbatim before the fix:

```
$ sh scripts/check/check-aspect-seal.shs --bogus ; echo rc=$?
ERROR — nothing was checked (unknown argument: --bogus)
rc=2
$ grep verdict_line build/evidence/check-aspect-seal.receipt
verdict_line=PASS — 1 aspect(s) checked, unbound-required=0 late-activation=0 post-weave-recheck=ran
```

Fix: `receipt_error()` in `scripts/check/lib/emit_receipt.shs`, called from a
`die_error()` helper that every ERROR path in the gate now routes through. It
records the ERROR verdict — which the census rejects via
`receipt_verdict_is_pass()` (`starts_with("PASS")`) as `verdict-not-pass` — and,
when the receipt cannot be written at all (one ERROR path IS a missing
`bin/simple`, the artifact `emit_receipt` must hash), DELETES the stale receipt
so the census reports `missing`. Both outcomes fail the seal.

Proven to discriminate end to end after the fix:

```
$ sh scripts/check/check-aspect-seal.shs --bogus ; echo rc=$?
ERROR — nothing was checked (unknown argument: --bogus)
rc=2
$ grep verdict_line build/evidence/check-aspect-seal.receipt
verdict_line=ERROR — nothing was checked (unknown argument: --bogus)
$ sh scripts/check/check-critical-release-seal.shs ; echo rc=$?
RECEIPT check-aspect-seal status=verdict-not-pass verdict=ERROR — nothing was checked (unknown argument: --bogus)
FAIL — 12 evidence receipt(s) checked, 12 not fresh: ... check-aspect-seal(verdict-not-pass) ...
rc=1
```

Before the fix that same sequence left the seal green. The remaining `missing`
entries are the pre-existing Phase 9 backlog, unrelated to this change.
