# `native-build` is broken outright at `origin/main` — every build dies with `cannot convert array to int`

- **Filed:** 2026-08-25
- **Status:** FIXED 2026-08-25 (lane-tipfix) — see § Resolution
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


---

# Resolution (2026-08-25, lane-tipfix)

## Offending commit

**`37d046a71b1` ("feat(smf): emit aspect pack section from driver")** — named by
`git bisect run` over the full 613-commit range, 10 steps, every BAD step
signature-checked so the result cannot be a different regression in the range.

The record's **commit** lead was therefore RIGHT. Its **mechanism** lead was
wrong, and the difference matters — see below.

## Endpoints, measured on ONE self-built seed

| commit | result |
|---|---|
| `cf6a439a57e` (tip at the time) | BAD — `cannot convert array to int`, all four error counters `0` |
| `5f2ad54578f` (last known good) | GOOD — artifact produced, runs, prints `hello` |

Both probed with the same freshly-`cargo build`-ed seed and the same runtime
archive. That is not just hygiene: `src/compiler_rust` changed **39 files /
+1923 lines** and `src/runtime` **1614 lines** inside the range, so a GOOD
result at `5f2ad54578f` on the tip-built seed is what rules **both** of them out
and isolates the defect to `src/**`. The original record did not address this.

## Root cause — a duplicate top-level `val` with a DIFFERENT TYPE

Two modules in one compile closure both declared `SMF_MAGIC`:

| file | declaration |
|---|---|
| `src/compiler/70.backend/linker/smf_header.spl:26` | `val SMF_MAGIC: [u8] = [83, 77, 70, 0]` |
| `src/compiler/70.backend/linker/smf_writer.spl:16` | `val SMF_MAGIC: i64 = 0x534D4600` |

`smf_writer.spl` **imports** `smf_header`, so both always coexist. Same-named
top-level `val`s resolve by last-definition-wins, so an `i64` consumer could
receive the `[u8]` **array** — and the seed interpreter's `as_int()`
(`src/compiler_rust/compiler/src/value_impl.rs:152`) then produces verbatim
`type mismatch: cannot convert array to int`. `SMF_FLAG_EXECUTABLE` collided the
same way (`i64 0x1` vs `u32 0x0001`), harmlessly, since the values agree.

**Both duplicated copies in `smf_writer.spl` were DEAD** — declared, never
referenced anywhere in the file. They cost nothing and broke everything.

This is the same documented defect family as
`seed_optional_query_comparison_divergence_2026-08-16.md` § private-import
divergence, whose in-tree note at
`src/lib/gc_async_mut/gpu/browser_engine/net/entity/request_types.spl:19`
records the identical error string from the identical cause.

## The commit EXPOSED the defect; it did not introduce it

`37d046a71b1` added one import to `src/compiler/80.driver/smf_writer.spl`:

```
use compiler.backend.linker.smf_writer.{smf_build_aspect_pack_image}
```

That pulled `compiler.backend.linker.smf_writer` into the driver's default
compile closure **for the first time**, and with it the latent collision. Three
experiments pin this, each a full hello-world `native-build`:

| tree state | result |
|---|---|
| tip, import deleted | **GOOD** |
| tip, import retargeted to a pre-existing symbol (`SectionType`), new aspect-pack code unreferenced | **BAD** |
| tip, the two NEW aspect-pack functions deleted from the linker module, import kept | **BAD** |
| tip, importing only the transitive dep `smf_header` | **GOOD** |

So neither the new aspect-pack code nor the transitive deps matter: merely
placing that module in the closure is sufficient.

## Refuted leads (recorded so they are not re-probed)

- **`add_assurance_note_section` / its `b as i64` byte loop — REFUTED.** It has
  **zero callers** in `src/`, as do its three siblings
  (`add_drv_manifest_section`, `add_launch_metadata_section`,
  `add_aspect_pack_section`). It cannot be on the hello-world path. The matching
  string in `assurance_object_note_spec.spl` is a spec-only coincidence.
- **"Fails after link" — REFUTED as a log artifact.** The `[build] link ...`
  lines come from the parent process; the worker's own stderr contains **no**
  `[build]` lines at all and ends at the error. The phases were interleaved in
  the original transcript.
- **Name-collision among functions — REFUTED.** A census of every top-level
  `fn` the linker module defines against all of `src/` found exactly one
  duplicate (`smf_align_up`), and both definitions are `(i64,i64) -> i64` with
  equivalent bodies. The compiler's own collision warning named only `env_get`,
  which is present in the GOOD tree too.

## Fix

`src/compiler/70.backend/linker/smf_writer.spl`: delete the two dead, colliding
declarations (`SMF_MAGIC`, `SMF_FLAG_EXECUTABLE`) and leave a comment explaining
why they must not come back. **Two lines of behaviour change.**

A targeted repair was chosen over reverting `37d046a71b1` because that commit is
correct: it is a landed feature with three passing spec callers, and it was the
*victim* of the defect, not its author. Reverting would have re-hidden a latent
collision that the next importer of that module would have tripped over again.

## Verification

- Hello world at tip: `PROBE: GOOD`, artifact runs, prints `hello`.
- Reproduce spec `test/01_unit/compiler/linker/smf_writer_duplicate_toplevel_val_source_spec.spl`:
  **pre-fix 2 total / 0 passed / 2 failed → post-fix 2/2 passed**, verified by
  stashing the source edit alone and re-running.
- Feature survives: `aspect_pack_smf_writer_spec.spl` 4/4,
  `aspect_catalog_invalidation_spec.spl` 8/8.
- `aspect_pack_smf_section_wiring_spec.spl` is 10 passed / 2 failed — **measured
  byte-identical at pristine tip**, so pre-existing and NOT caused by this fix.
  Stated rather than papered over; not investigated here.
- No Rust was touched, so `cargo check --release --bin simple` is unaffected.

## Why every existing gate stayed green — and the new one

Both existing hello-world gates are blind for STRUCTURAL reasons, each measured:

1. `check-native-build-hello-world-runs.shs` deliberately stops as soon as
   `[build] ... step 1/6` appears (documented: speed). This defect fails after
   that line.
2. `check-stage2-hello-world-native-build.shs` does assert artifact + output,
   but `--entry-closure` is **mandatory** on both its arms — and that flag is
   exactly what keeps the offending module out of the closure. **Measured: it
   reports `PASS — 2 case(s) checked` on the exact broken tree.**

So the uncovered axis is the **closure** axis, precisely as the argument-form
axis was for gate 2. New gate
`scripts/check/check-native-build-full-closure-hello-world.shs` covers that axis
and nothing else: default (full) closure, build to completion, artifact must
exist and must run and print. Proven in **both** directions against the real
tree — `FAIL — 1 case(s) checked, simple:full-closure:fail(build rc=1: error:
semantic: type mismatch: cannot convert array to int)` on the broken tree,
`PASS — 1 case(s) checked` with the fix. `--selftest` is fatal and runs first
(6 fixtures, including one pinning that `--entry-closure` is never
reintroduced). Cost is ~4-5 min, which is why it is a separate gate rather than
a third arm on gate 2: gate 2 runs per-candidate inside bootstrap admission, and
this is a property of the TREE, not of a candidate.
