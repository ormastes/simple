# phase2 bootstrap CLI cannot native-build a hello world on macOS aarch64 (`AOT compile error: <invalid-heap:…>`), SEGVs on the sspec scorer entry, and SEGVs compiling a struct-level generic
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-05 (macOS aarch64, `bin/local/phase2-aarch64-apple-darwin/simple`, 139,502,808 bytes, `simple-bootstrap 1.0.0-rc.1`)
**Status:** SUPERSEDED — blocks lane (a) of measuring the sspec score natively; a working
seed-interpreter lane exists instead (`scripts/check/sspec-score-seed-lane.shs`)

## 1. Hello world does not native-build (this, not `Id`, is the real blocker)

```
$ printf 'fn main() -> i64:\n    print "hello"\n    0\n' > build/nb/hello.spl
$ bin/local/phase2-aarch64-apple-darwin/simple native-build build/nb/hello.spl -o build/nb/hello
      reason: AOT compile error in build.nb.hello: <invalid-heap:0x984d6e8c1>
error: in-process native-build: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
rc=1
```

Identical with `--backend=cranelift` and `--backend=llvm` (different
`<invalid-heap:…>` addresses each run — a dangling/garbage heap value is being
formatted as the error text, i.e. the error message itself is corrupt).

## 2. The sspec scorer entry exits 139 after monomorphize completes

A minimal entry importing only `app.sspec_maintain.analyzer` (71 modules,
none of them `std.common.search`) gets through HIR (step 2) and monomorphize
(step 4) with 16 `[post-mono-verify] unhandled HirTypeKind variant at walk_type`
lines; the last log line is `[build] monomorphize ... step 4/6 ... complete`, no step-5 line follows, and the compiler exits **139** with no diagnostic. Log:
`build/nb/build.log` (2172 lines) when reproduced.

## 3. `unresolved type: Id` is a struct-level generic parameter — a resolution bug, not a missing type

`src/std/common/search/types.spl:251` declares `struct PostingList<Id>` and
`impl PostingList<Id>`; `Id` is its type parameter. `native-build
src/app/sspec_maintain/main.spl` reports `HIR lowering error in
src/std/common/search/ranking.spl: unresolved type: Id` because `main.spl`'s
import chain (`app.io.cli_ops` → …) reaches `std.common.search`. The analyzer
itself does not. Attempting to isolate it:

```
$ cat build/nb/gen.spl
struct Box<T>:
    v: T
impl Box<T>:
    fn get() -> T:
        self.v
fn main() -> i64:
    val b = Box(v: 3)
    print b.get()
    0
$ bin/local/phase2-aarch64-apple-darwin/simple compile --format=smf -o build/nb/gen.smf build/nb/gen.spl
rc=139        # SEGV after "[mono] generic_fns=0 call_sites=0 specializations=0 unresolved=0"
```

So the struct-generic path crashes before it can even report `unresolved
type`. Three independent defects, one binary. Related: the SMF that `compile`
does produce for a non-generic file is rejected by the Rust seed's loader
(`Invalid SMF magic number (tried both v1.1 trailer and v1.0 header)`), so
"compile with phase2, run with the seed" is not a lane either.

## Unblock condition

A phase2/stage4 binary that native-builds `build/nb/hello.spl`; then
`native-build build/nb/sspec_score_min.spl` (the analyzer-only entry) is the
proof that `simple sspec-maintain scan` can be built here. Sibling record from the same day, other lane: `stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`.


## Round-10 verdict note (2026-11-06)
Verdict: host-blocked. Needs the macOS aarch64 phase2 binary; not reproducible on this Windows host. Re-test the struct-generic SEGV on a Phase-3 stage binary: simple compile --format=smf build/nb/gen.spl

---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED (all three defects addressed on tip; e2e native re-run blocked)

Triage at release tip b364745fdbf8 (Windows host, refreshed seed 0791c2b7f4a7).

**Defect 3 (struct-level generic `unresolved type: Id`): FIXED.**
`crypto_digest_generic_struct_2026-06-15` was CLOSED 2026-09-13 with
"struct type parameter resolves inside its `impl` block" and its closure note
explicitly names this row's shapes (`PostingList<Id>`, `Embedding<D>`) as
covered by the same resolution. Fixing commit dc23f165150d ("generic fn/method
give clean #158 diagnostic; thread struct type params") is an ancestor of the
tip; later generic-struct MIR hardening also on tip (2cf0821e85a1, 25577096b822).

**Defect 2 (SEGV 139 after monomorphize with `[post-mono-verify] unhandled
HirTypeKind variant at walk_type`): SUPERSEDED by removal.** The 40.mono
monomorphization pass was deleted from the compiler (e.g. 56c0499ebd15 "remove
the remaining monomorphization references", ab9305d783e9 "remove every caller of
the deleted 40.mono pass"); `src/compiler/` no longer contains a mono pass
directory and neither `post-mono-verify` nor the walk_type message exists in
the tree. The failing path is structurally gone.

**Defect 1 (hello-world native-build fails, error text is `<invalid-heap:…>`):
MITIGATED on the symptom this row tracks.** The raising site now prints the
diagnostic eagerly: `_aot_compile_failure`
(driver_aot_native_output.spl:3456-3467) emits pure-literal + bare-print
name/reason + length lines BEFORE returning Err, precisely so the corrupt
`err.to_text()` crossing can no longer blind every failure. The underlying
`Err`-payload-crossing ABI defect remains OPEN and is tracked in its own row,
stage2_aot_error_message_lost_invalid_heap_2026-09-06.md (sibling; the
eager-print hardening comments cite it).

Seed-smoke verifications (2026-11-11, seed 0791c2b7f4a7):
- `bin/simple.exe compile --format=smf -o gen.smf build/nb/gen.spl` (the row's
  own struct-generic isolation repro) — rc=0; the produced SMF then runs
  correctly on the seed (`run gen.smf` prints `3`, rc=0), also under
  SIMPLE_EXECUTION_MODE=interpret. No SEGV, no `unresolved type`.

Blocked in-lane (needs grant): the row's actual unblock condition —
`native-build build/nb/hello.spl` and `native-build build/nb/sspec_score_min.spl`
on a stage2/stage3 binary — is a native/entry-closure build, forbidden in this
lane; the original repro host was macOS aarch64 (Round-10 already called it
host-blocked from Windows). Mechanism-level evidence above is the strongest
available in-lane.
