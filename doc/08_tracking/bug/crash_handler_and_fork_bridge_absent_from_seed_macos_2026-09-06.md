# BUG: the C crash handler and the fork bridge are absent from the Rust seed, so Phase 2 of the SIGSEGV hardening plan cannot be verified

**Status:** OPEN (blocked on a compiler deploy; no code fix attempted)

## 2026-09-16 update (macOS sweep)

**Source fix landed (not yet deployed — this record stays OPEN).** The handler
and the fork bridge now share a capsule: `_spl_fault_class`,
`_spl_crash_handler`, and `rt_install_crash_handler` moved verbatim from
`src/runtime/runtime.c` (former :2977-3045) to `src/runtime/runtime_fork.c`
(new section after the POSIX/Windows split). `runtime_fork.c` is a member of
BOTH native capsules' source lists — the seed core-C capsule
(`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs`,
`build_c_runtime_library`) and the pure-Simple backend
(`src/compiler/70.backend/backend/runtime_compiler.spl`, `compile_runtime_objects`)
— while `runtime.c` is compiled by the pure-Simple list only (the seed capsule
deliberately omits it: wholesale inclusion collides with `runtime_native.c`).
`runtime.c` keeps its forward declaration and the install call in the strong
`spl_init_args` (:1657/:1666), now resolving against the `runtime_fork.o`
definition; the Windows `#else` stub moved with it. One definition across both
lanes — no macro guards needed.

**The install call, not just the definition, was the seed-capsule gap.**
The only pre-existing call site was the STRONG `spl_init_args` in `runtime.c`
— a TU the seed capsule never links, so a definition-only move would have
left seed-capsule binaries with the symbol exported but never installed. The
WEAK `spl_init_args` in `src/runtime/runtime_native.c:5899` (the definition
the seed capsule actually links, reached from `rt_set_args` /
`__simple_runtime_init` at process start) now carries the same
`rt_install_crash_handler()` call, compiled `#ifndef _WIN32` (PE/COFF
weak-external resolution across TUs is unreliable there, and the handler is a
no-op stub on Windows anyway). Installing twice is harmless — sigaction with
the same handler and flags is idempotent. Every lane that compiles the new
call also compiles the definition (`runtime_native.c` and `runtime_fork.c`
have identical lane memberships: seed,simple), and ad-hoc compile sets
(`native.spl`, `leak_check/external_runner.spl`) compile `runtime.c` +
`runtime_fork.c` together, so no link set gains an unresolved reference.

**Verified WITHOUT a rebuild (this host, macOS aarch64):**

- `clang -c -std=gnu11 -I src/runtime` compiles all three touched files
  cleanly (`runtime.c`, `runtime_fork.c`, `runtime_native.c`, objects in
  /tmp). `nm` on the fresh objects: exactly ONE `T _rt_install_crash_handler`
  (in `runtime_fork.o`; the two static helpers are local `t`).
- `scripts/check/check-runtime-source-list-parity.shs`: **PASS — 155 file(s)
  checked, 0 drift**. The move changes no membership (runtime.c stays
  `simple`, runtime_fork.c stays `seed,simple`), so no row changed for it;
  the baseline did need two new `none` rows for the in-flight simple_browser
  lane's `browser/chrome_render_evidence_shim.c` /
  `browser/chrome_render_provider.c` (recorded in the baseline header).
- `scripts/check/check-runtime-symbol-lane-divergence.shs` (manual gate,
  compiles lanes B and C with the real cc): `ok=true` — the moved symbol
  produces no new cross-file duplicate pair.
- `nm build/simple-core/runtime_fork.o` (the seed-capsule build dir on this
  host): all `rt_fork_*` exported as global `T`, confirming symbols defined
  in `runtime_fork.c` are archive-visible; `rt_install_crash_handler` will
  appear here on the next capsule build. That dir contains no `runtime.o`,
  matching the tools.rs list.
- `bin/simple test test/01_unit/lib/crash/crash_bundle_spec.spl`: the new
  Phase-2 fork example **skip-passes on the seed** via a visible skip, the
  three std.log ring-record examples fail exactly as the unmodified HEAD
  version of this spec does on this seed (proven pre-existing via
  `git show HEAD:` extract — unrelated to this change).
- `bin/simple test test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`:
  **7/7 pass** — the Phase-2 needle (`crash_bundle_spec.spl` contains
  `rt_fork_parent_wait`) flips green; the si_code example now reads
  `runtime_fork.c` (where the handler lives after the move) and stays green.

**Why the fork example is nm-gated rather than nil-gated.** `simple test`
forces the interpreter lane, where calling an unbacked extern is a HARD error
(`semantic: unknown extern function`, rc=1) — the silent-nil substitution is
JIT-lane only (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`,
measured again today). So the example probes the deployed tool's symbol table
(`nm bin/simple | grep rt_fork_child_setup`, the same oracle this record's
unblock condition uses; `bin/simple` is the symlink to the deployed tool, and
empty-vs-non-empty comparison is newline-safe). No existing spec feature-detects
unbacked externs at runtime under the interpreter lane; this follows the
kv260 spec's `rt_process_run("/bin/sh", ...)` shell-probe idiom. On a binary
with the fork bridge but without the crash handler (the state of the CURRENT
darwin release binaries), the example still runs and fails honestly on the
parent-side banner assertions — the correct polarity. On the seed it asserts
the skip predicate itself, so it is not a green-that-asserts-nothing.

**Sweep correction to the root-cause line above.** `nm` on this host shows
`bin/release/aarch64-apple-darwin/simple` DOES export runtime.c symbols
(`spl_init_args`, `spl_arg_count`) yet lacks `rt_install_crash_handler` — it
links `runtime.o` from BEFORE the handler landed in source. The
`-macho` sibling exports no `spl_init_args` at all (seed-capsule build). Both
lack the handler for the same underlying reason the record names — no
deployed binary was ever rebuilt with the handler — but "the deployed
self-hosted capsule links runtime_fork.o but not runtime.o" is only true of
the macho lane's capsule.

**What remains (deployment, out of scope for this lane):**

1. Rebuild the seed core-C capsule (next `build_c_runtime_library` run picks
   up the moved handler + the weak-spl_init_args install call) and rebuild
   the self-hosted darwin binaries (both `bin/release/aarch64-apple-darwin`
   and `-macho`) from this source.
2. Repoint `bin/simple` off the Rust seed binary
   (`src/compiler_rust/target/bootstrap/simple`, the rust lane
   `compiler_rust/runtime/build.rs`, which compiles NEITHER `runtime.c` NOR
   `runtime_fork.c` — this source change alone cannot add any C symbol to
   it) and onto a capsule-linking self-hosted binary.
3. Re-run the nm counts (`rt_fork_*` and `rt_install_crash_handler` non-zero
   in the deployed binary) and the probe: the null-deref program must return
   `rc=139` with the `[simple-runtime] Fatal: SIGSEGV ... (si_code=...)`
   banner plus `Backtrace:` on stderr; then the crash_bundle_spec Phase-2
   example fires its real parent-side assertions
   (`rt_fork_parent_wait(pid, 10000) == 139`,
   `rt_fork_parent_signaled() == false`, stderr containing both needles).
   Note: `bin/release/aarch64-apple-darwin/simple test` on the CURRENT stale
   binaries cannot even parse the tree today — the concurrent simple_browser
   lane's in-flight `src/lib/nogc_sync_mut/io/process_ops.spl` does not parse
   against it; unrelated and off-limits.

Files touched: `src/runtime/runtime.c` (handler block replaced by a pointer
comment; forward-decl comment updated), `src/runtime/runtime_fork.c`
(handler block added), `src/runtime/runtime_native.c` (weak spl_init_args
installs the handler on non-Windows), `scripts/check/runtime_source_list_parity_baseline.txt`
(two browser-shim rows + header note), `test/01_unit/lib/crash/crash_bundle_spec.spl`
(Phase-2 fork example + nm probe), `test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`
(file pointers to the moved handler). Nothing committed.

---

**Found:** 2026-09-06, macOS aarch64 (Darwin 25.5.0)
**Binary under test:** `src/compiler_rust/target/debug/simple` (the only binary
this lane is permitted to use; a bootstrap is forbidden this session)
**Blocks:** the first example of
`test/03_system/plan_acceptance/serial_sigsegv_and_test_hardening_spec.spl`
("A null-pointer deref in compiled mode recovers into a backtrace, not a bare
process crash"), i.e. Phase 2 of
`doc/03_plan/infra/audit/serial_sigsegv_and_test_hardening.md`.

## What the plan promises

`rt_install_crash_handler` (`src/runtime/runtime.c:2755`) installs
`_spl_crash_handler` for SIGSEGV/SIGBUS. That handler is real and complete: it
classifies `si_code` through `_spl_fault_class` (`runtime.c:2709`), writes
`[simple-runtime] Fatal: <signame> at address <addr> (si_code=N: <class>)` plus
a `Backtrace:` dump with async-signal-safe `write()`, and ends in
`_exit(128 + signum)`. `runtime.c:1647` calls it at process start.

The acceptance oracle asks for a spec that drives a genuine fault through it:
fork a child, crash it, and read `rt_fork_parent_stderr()` /
`rt_fork_parent_signaled()` the way
`src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl` already does.

## What is actually in the permitted binary

```
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_fork_child_setup|rt_fork_parent_wait|rt_fork_parent_stderr|rt_fork_parent_signaled'
0
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_install_crash_handler'
0
$ nm src/compiler_rust/target/debug/simple | grep -cE 'rt_ptr_write_i64'
2
```

The fork bridge and the crash handler are not linked into this binary at all.
Only the raw pointer primitive is.

## Behavioural confirmation

```
extern fn rt_ptr_write_i64(addr: i64, offset: i64, value: i64)

fn main():
    print "before"
    rt_ptr_write_i64(0, 0, 1)
    print "after"
```

```
before
rc=134
```

`134` is SIGABRT (a Rust-side abort), not `139` (`128 + SIGSEGV`), and no
`[simple-runtime] Fatal:` banner and no `Backtrace:` appear on stderr. The C
crash handler is not installed in this process. This is the "bare process
crash" the oracle exists to rule out — the oracle is honestly RED here.

## Why nothing was changed

Writing the promised fork test into
`test/01_unit/lib/crash/crash_bundle_spec.spl` would satisfy the acceptance
oracle's `contains("rt_fork_parent_wait")` needle while turning
`crash_bundle_spec.spl` itself red on this host, because
`rt_fork_child_setup` / `rt_fork_parent_wait` are unbacked here and an unbacked
extern returns nil silently (see
`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`). That trades
one honest red for a green that asserts nothing plus a new red elsewhere.
`test/01_unit/lib/crash/crash_bundle_spec.spl` was therefore left untouched and
the acceptance example left failing.

## Unblock condition

A deployed binary that links `src/runtime/` (the C runtime archive), verified
by the `nm` counts above becoming non-zero and by the probe returning `rc=139`
with the `[simple-runtime] Fatal: SIGSEGV ... (si_code=...)` + `Backtrace:`
banner. At that point the spec to write asserts, on the parent side:
`rt_fork_parent_wait(pid, 10000) == 139`, `rt_fork_parent_signaled() == false`
(the handler intercepted and `_exit()`ed, so the child is WIFEXITED, not
WIFSIGNALED — asserting `true` here would be asserting the failure mode), and
`rt_fork_parent_stderr()` containing both `[simple-runtime] Fatal:` and
`Backtrace:`.
