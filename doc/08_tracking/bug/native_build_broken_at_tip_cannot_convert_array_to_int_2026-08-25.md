# `native-build` is broken outright at `origin/main` — every build dies with `cannot convert array to int`

- **Filed:** 2026-08-25
- **Status:** OPEN — blocking
- **Severity:** blocks the entire native lane, and with it
  `scripts/check/check-engine-differential.shs` (one of the 12 obligations in
  the critical-release seal).
- **Confirmed broken at:** `e8db788629b` ("feat(simpleos): stage signed media
  and bounded reattestation"). `origin/main` has since moved to `73d6deb5f66`;
  the new tip has NOT been probed.
- **Last known good:** `5f2ad54578f` ("fix(check): close the same
  receipt-laundering hole in check-engine-differential").
- **Range to bisect:** `5f2ad54578f..e8db788629b` — **608 commits**.

## Symptom

In a fresh `git worktree` checked out at the tip, with a freshly built seed
(`cargo build --release --bin simple`), **every** `native-build` fails —
including a three-line hello world with no arrays in it at all:

```
$ printf 'fn main() -> i64:\n    print("hello")\n    0\n' > scratch/gf/hw.spl
$ ./bin/simple native-build scratch/gf/hw.spl -o /tmp/hw.bin
rc=1   artifact=NO
error: semantic: type mismatch: cannot convert array to int
```

The same command in the same worktree at `5f2ad54578f`:

```
rc=0   artifact=YES
$ /tmp/hw3.bin
hello
```

Same seed binary, same worktree, same runtime archive — only the checked-out
compiler sources differ. That isolates the defect to `src/**` content in the
range above.

## Why the message is misleading

`semantic:` is a driver label, not a phase. The failure happens **after** the
build reports success:

```
[build] native_compile 1/1 step 5/6 +1418ms dt=332ms complete
[build] link 1/1 step 5/6 ...
[build] link 1/1 step 6/6 +1819ms dt=401ms ...
[bootstrap-error-count] source_idx=0 point=post-lowering  count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
[bootstrap-error-count] source_idx=0 point=post-store     count=0
error: semantic: type mismatch: cannot convert array to int
```

Every error counter is zero and the link step completes; the `.tmp` artifact is
then never renamed, so callers see "no artifact produced". The text comes from
the Rust seed's `value_impl.rs:152` (`as_int()` on a `Value::Array`) — i.e. the
pure-Simple compiler, running under the seed interpreter, called `.as_int()` on
something that is an array at runtime. It is a **crash in the driver**, not a
diagnosis of the user program.

## Suspected site

`doc/08_tracking/bug/compiler_tree_spec_sweep_triage_2026-08-23.md` already
records the identical string in the linker:

> `compiler/linker/assurance_object_note_spec.spl`, 1/5 —
> `semantic: type mismatch: cannot convert array to int` in
> `add_assurance_note_section`.

`src/compiler/70.backend/linker/smf_writer.spl:308` is that function, and its
body is a byte loop with an `as i64` cast:

```
        val bytes = note.to_bytes()
        var payload: [i64] = []
        for b in bytes:
            payload.push(b as i64)
        self.add_note_section(".assurance_note", payload)
```

If `to_bytes()` yields rows rather than scalars, `b as i64` is exactly an
array-to-int cast. Directly above it sits
`add_aspect_pack_directory_section`, and `37d046a71b1` ("feat(smf): emit
aspect pack section from driver") — inside the bisect range — newly drives that
region from the driver. That commit and its parent `c0ebc33ff2b` are the first
pair to probe.

**This is a lead, not a root cause. Bisect before believing it.**

## Reproduce / bisect recipe

The hello-world probe above is the bisect predicate: ~2 minutes per step, ~10
steps for 608 commits. It needs only a seed binary and `build/simple-core`
copied into the worktree.

## Consequence for the differential gate

`check-engine-differential.shs`'s native lane cannot run at the tip at all —
every fixture reports `LANE_ERROR -- native-build produced no artifact`, and
with fewer than two answering lanes the gate degrades to
`INCONCLUSIVE`/`ERROR` rather than comparing anything. Any recent claim that
the gate is green must therefore have been measured on an older tree; the
13-fixture measurements circulating in this session correspond to
`5f2ad54578f`, which carries 13 fixtures (the tip carries 17).
