# phase2 bootstrap CLI cannot native-build a hello world on macOS aarch64 (`AOT compile error: <invalid-heap:…>`), SEGVs on the sspec scorer entry, and SEGVs compiling a struct-level generic

**Date:** 2026-09-05 (macOS aarch64, `bin/local/phase2-aarch64-apple-darwin/simple`, 139,502,808 bytes, `simple-bootstrap 1.0.0-rc.1`)
**Status:** OPEN — blocks lane (a) of measuring the sspec score natively; a working
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
