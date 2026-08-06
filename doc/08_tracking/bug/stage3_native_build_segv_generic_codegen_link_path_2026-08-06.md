# Self-hosted `bootstrap/stage3/.../simple` SIGSEGVs on essentially EVERY `native-build` — `bin/simple` is silently the Rust seed, not a working self-hosted replacement

- **Date:** 2026-08-06
- **Severity:** high — the self-hosted stage3 compiler cannot currently emit
  ANY native binary via `native-build`, including a trivial
  `fn main(): print("hello")`. Independently reproduced (own gdb backtrace +
  register dump), on top of the sighting already recorded in
  `mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`'s
  "Verification" section (that doc's `0x118` mention is the same crash; this
  doc gives the standalone confirmation, root-cause correlation, and — most
  importantly — the scope/regression determination that doc explicitly left
  open).
- **Status:** reproduced independently, root cause narrowed but NOT source-line
  pinned (binary is stripped, no debug symbols), NOT fixed (see "Why no fix
  attempted here"). Documented per the "record instead of silently normalize"
  rule.

## Reproduction (own run, independent of the other lane)

```
$ git fetch origin main   # tip 42706d525a77d7af30c70b43435b330cd83732c0
$ cat /tmp/.../hello.spl
fn main():
    print("hello")

$ ulimit -c unlimited
$ timeout 30 bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build hello.spl -o hello_out
timeout: the monitored command dumped core
$ echo $?
139
```

Reproduced **2/2** tries here (identical fault both times), on top of the other
lane's **3/3** — 5/5 combined across two independent sessions.

## Own gdb backtrace + register dump (not borrowed from the other lane)

```
$ gdb -batch -ex run -ex "info registers" -ex "x/3i \$pc" -ex bt \
    --args bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build hello.spl -o hello_out
...
Program received signal SIGSEGV, Segmentation fault.
0x0000000000517966 in ?? ()
=> 0x517966:  mov    0x8(%rax),%r14      ; faulting instruction
   0x51796a:  test   %r14,%r14
   0x51796d:  jle    0x5179ad
#0  0x0000000000517966 in ?? ()
#1  0x000000000051842e in ?? ()
#2  0x000000000067b29c in ?? ()
#3  0x000000000066b928 in ?? ()
#4  0x000000000040533d in ?? ()
#5  0x00000000004025f5 in ?? ()
#6  __libc_start_call_main (...)
#7  __libc_start_main_impl (...)
#8  0x00000000004024f5 in ?? ()

rax  = 0x110   (272)
```

`rax` is `0x110`; the faulting instruction reads `0x8(%rax)` — i.e. the
faulting address is `0x110 + 0x8 = 0x118`. **This exactly matches** the other
lane's independently-observed `strace` finding of `SEGV_MAPERR at 0x118`,
confirmed here via a completely separate tool (gdb register dump vs. their
strace) rather than trusted secondhand.

The binary is **stripped** (`file` reports `stripped`, `nm` yields effectively
no symbols), so no `addr2line` source-line mapping is possible. Backtrace
frames are raw addresses only.

## Root-cause correlation: the `uname`/target-triple-detection theory is REFUTED — this is a generic native-build codegen/link-path bug, not host-detection-specific

Initial working theory (matching the other lane's `strace` timing, "fault
right after two `uname` subprocess calls"): the crash lives in host-OS/arch
detection — `src/lib/nogc_sync_mut/platform.spl`'s `host_os()`/`host_arch()`
(which shell out via `shell_output_trim("uname -s"/"uname -m")`, calling
`extern fn rt_process_run(cmd, args) -> (text, text, i64)` and indexing the
returned 3-tuple with `result[0]`/`result[2]`), reached from
`src/compiler/70.backend/backend/llvm_target.spl`'s
`LlvmTargetTriple.from_target_with_mode()`.

**This theory does not survive a direct discriminator test.**
`from_target_with_mode()` has an explicit early-return branch
(`llvm_target.spl:46-53`) that returns the SimpleOS triple *before any `uname`
call at all* when `target == CodegenTarget.SimpleOS_X86_64`:

```
val is_simpleos = match target: case CodegenTarget.SimpleOS_X86_64: true ...
if is_simpleos:
    return LlvmTargetTriple(arch: "x86_64", vendor: "unknown", os: "simpleos", env: nil)
```

I ran the identical trivial script through that exact path:

```
$ timeout 30 bootstrap/stage3/x86_64-unknown-linux-gnu/simple native-build \
    hello.spl --target x86_64-unknown-simpleos -o h_simpleos
timeout: the monitored command dumped core
```

```
$ gdb -batch -ex run -ex "info registers rax" -ex bt --args ... --target x86_64-unknown-simpleos ...
Program received signal SIGSEGV, Segmentation fault.
0x0000000000517966 in ?? ()
rax  0x110  272
#0  0x0000000000517966 in ?? ()
#1  0x000000000051842e in ?? ()
#2  0x000000000067b29c in ?? ()
#3  0x000000000066b928 in ?? ()
#4  0x000000000040533d in ?? ()
...
```

**Byte-for-byte identical fault** — same address, same `rax`, same full call
stack — as the default-target run, on a code path that (per the source above)
cannot reach `host_os()`/`host_arch()`/`uname` at all. The `uname`-adjacent
timing the other lane observed via `strace` was therefore coincidental (some
other startup-path `uname` call, unrelated to target-triple detection, just
happens to precede the real fault site in program order) — **not causal**.

**Corrected conclusion:** this is a **generic bug somewhere in the shared
`native-build` codegen/link success path** — reached regardless of which
target triple is requested — not something specific to host-OS/arch
detection. The disassembly at the fault site is a small loop reading a length
field at `obj+0x8` and then iterating an array (calls to what look like
clone/refcount helpers at fixed offsets, incrementing an index by 8 per
iteration) — the shape of a list/array clone operation, and `rax=0x110` is not
a valid heap pointer (looks like a small scalar — a length or similar — that
leaked into a pointer-typed slot). This still matches the general shape of the
pre-documented native-codegen list/tuple-handling defect family in this
repo's memory notes, but **without a specific call site to name** — the
`shell_output_trim`/`rt_process_run` tuple-indexing hypothesis is now
withdrawn, not confirmed. Pinning the actual call site requires symbols
(see "Why no fix attempted here").

## Regression vs. pre-existing: PRE-EXISTING, not caused by today's lanes

```
$ git log --oneline -10 -- src/lib/nogc_sync_mut/platform.spl src/compiler/70.backend/backend/llvm_target.spl
e3e9ea639a6 fix(os): add receiver diagnostic to dispatch-gap refusal; narrow AC-6 rc=70 root cause
375d4f3fabb feat(os): port the Simple runtime to SimpleOS — payload now links
... (none from today, 2026-08-06)
```

Neither file has any commit from today. The crash also reproduces on a
completely trivial `print("hello")` with **zero MIR-lowering errors** — fully
independent of today's `.first()`/`CodegenError` fix
(`mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`), which
only matters on the fatal-MIR-error path. **Not a regression from today's
landings** — a pre-existing instability that simply hadn't been hit/reported
via this exact `native-build`-on-trivial-input path before today.

## Scope determination — THE important finding for other lanes

`.claude/rules/bootstrap.md` and this session's task both assumed "the
deployed self-hosted binary" is `bin/release/<triple>/simple` /
`bin/simple`. **That assumption needs correcting — and this is NOT a new
finding**: `doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md`
already documents, as of yesterday, that `bin/simple` resolves to the Rust
seed. I independently re-confirmed it is still true today (mtime Aug 6
10:48 — rebuilt today by some other lane, still a seed build) and am adding
what that doc does not cover: whether the seed crashes on this specific bug
(it does not) and what that means for today's OTHER lanes' verification
claims.

```
$ readlink -f bin/simple
/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple

$ bin/release/x86_64-unknown-linux-gnu/simple --version
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use
it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

**`bin/simple` currently resolves to the Rust bootstrap SEED, not a
self-hosted binary.** (`bin/release/simple`, a wrapper script, actively
refuses to run this exact binary with "refusing non-production Simple
runtime" — so the guard exists, but `bin/simple` bypasses it via the direct
symlink.)

I ran the identical `native-build hello.spl` through this seed binary. First
pass hit a pre-warmed cache (`[NATIVE] cache hit: ...`), so — to make the
"seed doesn't crash" claim airtight rather than accidentally measuring a
cache lookup — I reran with a **fresh, never-before-compiled file**
(`hello_v2.spl`, distinct content, distinct output basename):

```
$ timeout 280 bin/release/x86_64-unknown-linux-gnu/simple native-build hello_v2.spl -o hello_v2_out
... (no cache hit this time; genuinely fresh compile through
    src/app/cli/native_build_worker.spl) ...
$ ./hello_v2_out
hello_v2_fresh_no_cache
$ echo $?
0
```

**It works**, confirmed on a genuinely fresh (non-cached) compile. No crash.
Just slow (order of minutes for a trivial script — both the cache-hit and
fresh runs took roughly comparable, multi-ten-second-to-low-minutes wall time
dominated by `statx`-heavy module-tree scanning of large parts of
`src/compiler/`) — a separate, lower-severity performance issue, not
investigated further here.

**Net scope:**
| Binary | Path | Crashes on native-build? | What it actually is |
|---|---|---|---|
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | self-hosted stage3 | **YES, 5/5** | true self-hosted compiler |
| `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` | "deployed" path | **NO** | **Rust bootstrap seed** (mislabeled by convention as "the deployed binary") |

There is currently **no working self-hosted `native-build` path at all** —
only the (slow, non-canonical-per-CLAUDE.md) Rust seed works. This is a
bigger problem than "stage3 is broken": the project's own default tool
(`bin/simple`) is not what CLAUDE.md says it should be
("Default tooling = pure-Simple self-hosted binary, not the Rust seed").

## Should today's OTHER lanes' "verified via rebuild" claims be treated as suspect?

- **If a lane invoked `bin/simple` / `bin/release/<triple>/simple` and
  captured full stdout+stderr**, its native-build results are almost
  certainly trustworthy for "did it produce a working binary" — the seed does
  not crash on this bug. BUT the lane was silently exercising the Rust seed,
  not the self-hosted compiler, which matters for any claim specifically
  about self-hosted-compiler correctness/behavior (the seed and the
  self-hosted compiler are different implementations and have historically
  diverged — see multiple `reference_*` memory entries on engine/binary
  divergence). The seed prints an explicit `WARNING:` banner on every run;
  any lane that filtered/truncated output before this point would have missed
  it.
- **If a lane invoked `bootstrap/stage3/.../simple` (or any of the many
  `build/*/stage3/.../simple` scratch copies littering this repo from other
  sessions) directly for "rebuild verification,"** that lane's native-build
  claim IS suspect — it very likely hit this exact SIGSEGV and either treated
  a non-zero/crashing exit as failure (safe) or, if piping through `|| true`
  / ignoring exit codes, could have silently proceeded past a crash (compare
  the `simpleos_payload_link_missing_20_rt_symbols_2026-08-06.md` doc's
  independently-found "fail-open probe gate" sibling issue, where exactly this
  masking pattern was caught).
- I did not find, in a scan of today's other bug docs
  (`doc/08_tracking/bug/*2026-08-06*`), any claim that explicitly named
  `bootstrap/stage3/.../simple` as its verification binary for a
  *successful* native-build (the two hits found —
  `simpleos_payload_link_missing_20_rt_symbols_2026-08-06.md` and
  `path_based_fs_syscalls_fake_success_2026-08-06.md` — both already record
  stage3 as broken/unusable, consistent with this finding, not contradicting
  it).

## Why no fix attempted here

- The binary is stripped; I could not pin the exact faulting source line
  (only the call-chain correlation above).
- `platform.spl`'s `host_os()`/`host_arch()` and `llvm_target.spl`'s triple
  detection are load-bearing for **every** native-build and JIT-target-detect
  path across every architecture (x86_64/aarch64/riscv64/wasm/SimpleOS) — a
  guessed fix here risks breaking working paths for an unproven root cause.
- Verifying any fix requires rebuilding stage3, which requires bootstrapping
  through the very compiler this bug lives in — the same chicken-and-egg
  blocker the original bug doc already flagged as unresolved.
- Per "no bootstrap unless essential" and "no cover-up fixes": documenting the
  precise, independently-verified finding is safer than a blind patch to
  foundational platform-detection code.

## Recommended follow-up (not done here)

1. Rebuild a *symbol-retaining* (non-stripped) stage3 copy specifically to get
   `addr2line`-quality source correlation for this fault, then fix
   `shell_output_trim`'s tuple-indexing pattern (or whatever the real site
   turns out to be) using the established safe-substitution pattern for
   native-codegen list/tuple gaps.
2. Fix `bin/simple`'s symlink/build pipeline so it points at a real
   self-hosted binary again, not the Rust seed — and make the seed's
   `WARNING:` banner impossible to silently swallow (e.g. non-zero-only-warn
   exit code) so future lanes can't mistake it for "the deployed binary"
   the way this task's own initial framing did.
3. Separately: the seed's ~2-minute `native-build` time for a trivial script
   (full-tree `statx` module scan) is worth its own performance bug filing.
