# `native-build` is dead for EVERY input — nil-deref in the interpreted compiler

- **Status:** OPEN (reproduced at pristine `origin/main`, not diagnosed to a line)
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
