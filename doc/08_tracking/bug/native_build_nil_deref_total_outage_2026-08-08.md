# `native-build` is dead for EVERY input — nil-deref in the interpreted compiler

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  already fixed by `100a9aadcc4` *three minutes before this doc was filed*. This
  report was **stale on arrival**; see "Resolution" below. No action needed.
- **Date:** 2026-08-08
- **Severity:** critical — the entire native/MIR lane is unusable, and every
  MIR-level verification loop in the repo is silently blocked behind it
- **Measured at:** `origin/main` `6246f3104db`, in a **detached worktree pinned
  to that commit** (`git worktree add --detach`), not in the shared working copy

## Symptom

```
bin/simple native-build <any file> -o /tmp/x
  -> error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
     error: native-build worker exited with code 1.
     rc=1
```

This is a nil-deref **inside the interpreted pure-Simple compiler**, not a
diagnostic about the user program.

## It is not input-specific — this is the load-bearing evidence

Three inputs, same pinned worktree, identical failure:

| input | result |
|-------|--------|
| `test/fixtures/repro/compiler/primitive_trait_impl_dispatch_native_min.spl` | `undefined field 'kind'`, rc=1 |
| a struct + trait control (`impl Marker for Pt`) | `undefined field 'kind'`, rc=1 |
| **a two-line hello-world** (`fn main(): print("hello = " + (1 + 2).to_text())`) | `undefined field 'kind'`, rc=1 |

A two-line hello-world failing is what makes this a total outage rather than a
front-end gap in some feature.

## How far the pipeline gets

`50.mir` is reached — `[mir-method-call] start method=to_text argc=0` fires
(an unconditional `eprint` that already lives at
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:907` on
`origin/main`). Exactly **one** method call is lowered, then the nil-deref
aborts the run. So the crash is at or after MIR method-call lowering, and the
semantic phase completed.

## Prime suspect: the deployed worker binary, NOT an origin/main source regression

`native-build` spawns a worker interpreted by
`bin/release/x86_64-unknown-linux-gnu/simple`. That binary is gitignored and
was **redeployed 2026-08-08 00:53:07 UTC**, i.e. hours before this measurement
and one day after the last known-good native-build result. The binary is
invoked from the main repo path even when cwd is a pinned worktree, so a
worktree pin does NOT isolate it. Check the binary before bisecting source.

Precedent for exactly this shape:
`.claude/memory/reference_deployed_binary_lost_llvm_codegen_2026-07-29.md`,
`.claude/memory/reference_live_bin_simple_lost_all_subcommands_2026-08-01.md`.

## Regression window

`doc/08_tracking/bug/primitive_receiver_trait_impl_dispatch_2026-08-07.md`
records a lane getting real MIR output (`MIR lowering error: unresolved method
call: mark`, twice) from
`primitive_trait_impl_dispatch_native_min.spl` on 2026-08-07. Today the same
file on the same command dies before producing it. So the outage appeared
within roughly one day. Not bisected — see the binary suspicion above first.

## SEPARATE TRAP FOUND WHILE MEASURING — `native-build` truncates the MIDDLE of stderr

`src/app/cli/native_build_main.spl:185` `eprint_bounded` with
`OUTPUT_LIMIT = 12000` (line 61) prints the **first 6000 and last 6000
characters** and discards everything between, leaving only
`[stderr truncated by native-build entry]`.

Compiler diagnostics land in the discarded middle. On this fixture the raw
stderr is ~3000 lines; the bounded form showed ~1700. **Any
`grep -c '<diagnostic>'` over `native-build` output is therefore fail-open: a
count of 0 can mean "truncated away", not "absent".** This silently
invalidates trace-count oracles, which is precisely how MIR-level fixes in this
repo are normally verified.

Workaround while measuring: raise `OUTPUT_LIMIT` in a throwaway worktree and
confirm the truncation marker count is 0 before trusting any count.

## Reproduce

```
git worktree add --detach /tmp/pin origin/main
cd /tmp/pin
printf 'fn main():\n    print("hi")\n' > test/fixtures/repro/compiler/zz_hello.spl
/path/to/repo/bin/simple native-build test/fixtures/repro/compiler/zz_hello.spl -o /tmp/out
```

## Why this matters beyond itself

Any lane whose verification runs through `native-build` — the primitive-receiver
trait dispatch recipe above is one — cannot produce a RED or a GREEN today. The
correct response to such a lane reporting "0 errors" right now is to treat it as
UNVERIFIED, not as fixed: both the outage and the stderr truncation above
produce a clean-looking zero.

---

## Resolution (2026-08-08, verification lane)

**The outage was real, and it was already fixed before this doc landed.**

Fixed by `100a9aadcc4` *fix(mir): stop wrapping an already-optional receiver
type in Some()* (2026-08-08 01:21:40 UTC), which changed exactly the file this
report pointed at — `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
— and shipped its own record,
`doc/08_tracking/bug/..._method_call_some_wrap_nil_kind_crash_2026-08-08.md`.

This doc was committed at 01:24:31, but was **measured at `6246f3104db`
(01:05:47), which does not contain `100a9aadcc4`**. So it described a state
that no longer existed on `origin/main` by the time it was written.

### Current measurement (worktree pinned to `origin/main` `867c724e7bd`)

| input | rc | result |
|-------|----|--------|
| two-line hello-world | **0** | 27KB executable produced; running it prints `hello = 3` |
| `primitive_trait_impl_dispatch_native_min.spl` | 1 | `MIR lowering error: unresolved method call: mark` — the **pre-existing** 2026-08-07 state, not the nil-deref |

A nil-deref abort cannot emit a working binary, so rc=0 plus a binary that runs
is evidence no amount of output truncation can fake. (Do **not** use
`grep -c "undefined field 'kind'" == 0` as evidence here — that is exactly the
fail-open documented below.)

### Causation proven by revert

In the pinned worktree, restoring only `method_calls_literals.spl` to
`100a9aadcc4^` and re-running the same hello-world reproduces the failure
exactly — `rc=1`, `undefined field 'kind': cannot access field on value of type
'nil'`, no output binary. Restoring the file returns it to rc=0. One file, one
commit, both directions.

This also settles a side question: the worker **does** read the pinned
worktree's compiler sources, so a worktree pin is a valid isolation boundary
for `.spl` compiler changes.

### The deployed worker binary is EXONERATED

`bin/release/x86_64-unknown-linux-gnu/simple` (redeployed 00:53) was the prime
suspect. The *same* binary now produces rc=0. This was a **source defect, not
deployment skew** — the worker interprets `.spl`, so compiler-source edits are
live with no rebuild. **No redeploy is or was required.**

### Why it looked like a hang

A two-line hello-world native-build takes **~68s** in a clean worktree and
**~144s** in the shared working copy. Reproduction attempts capped at 120s time
out with no output and read as a total hang. Budget >300s.

### Unrelated observation

The fixture's log also carries `unsupported MIR type kind [infer-arm]:
HirTypeKind::Infer((0, 0))`, which is not in the 2026-08-07 record. Possibly
pre-existing and merely unlogged; flagged, not investigated.
