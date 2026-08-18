# Four `rt_*` symbols are defined in BOTH the Rust and C runtimes; `--whole-archive` turns that into a link failure for `simple-native-all`

- **Filed:** 2026-08-17
- **Status:** FIXED 2026-08-17 — link succeeds, `test result: ok. 12 passed; 0
  failed`. **The diagnosis in the body below is WRONG and is kept only as the
  record of what was believed; see "Actual root cause" and "Resolution".** The
  duplicates were Rust-vs-Rust (`simple-runtime` rlib vs `simple-native-all`'s
  own cgu), not Rust-vs-C, and no C file was involved or changed.
- **Severity:** High — blocks `cargo test --release` from producing a linked test
  binary for `simple-native-all`.
- **Component:** `src/compiler_rust/runtime/**`, `src/runtime/*.c`,
  `src/compiler_rust/runtime/build.rs`
- **Related:** `doc/08_tracking/bug/seed_build_guard_checks_only_bin_target_no_link_2026-08-17.md`
  (why two separate guards are both blind to this)

## Symptom

The `simple-native-all` lib test compiles and then fails to **link**:

```
rust-lld: error: duplicate symbol: rt_file_atomic_write
rust-lld: error: duplicate symbol: rt_mem_snapshot_open
rust-lld: error: duplicate symbol: rt_mem_snapshot_close
rust-lld: error: duplicate symbol: rt_mem_snapshot_record
```

## The two definitions of each symbol

| symbol | Rust definition | C definition |
|---|---|---|
| `rt_file_atomic_write` | `runtime/src/value/sffi/file_io/file_ops.rs:365` | `src/runtime/runtime_native.c:9496` |
| `rt_mem_snapshot_open` | `runtime/src/mem_snapshot.rs` | `src/runtime/runtime.c` **and** `src/runtime/runtime_legacy_core.c` |
| `rt_mem_snapshot_close` | `runtime/src/mem_snapshot.rs` | same two C files |
| `rt_mem_snapshot_record` | `runtime/src/mem_snapshot.rs` | same two C files |

Note the snapshot trio is defined **three** times each, not twice — two C files
plus Rust.

## Mechanism — why it fails only here

`runtime/build.rs:265-274`:

```rust
if env::var_os("CARGO_FEATURE_RUNTIME_SYMBOL_TABLE").is_some() {
    // A runtime-symbol-table cdylib promises that every registered C
    // provider is dynamically available. Normal selective archive
    // extraction drops providers that are referenced only through the
    // generated table ...
    println!("cargo:rustc-link-lib=static:+whole-archive=runtime_sffi_c");
} else {
    println!("cargo:rustc-link-lib=static=runtime_sffi_c");
}
```

This explains the whole shape of the bug:

- **Without** `runtime-symbol-table`, `libruntime_sffi_c.a` is linked
  *selectively*. The linker pulls only the archive members it needs; since the
  Rust crate already defines those four symbols, the C members holding them are
  never pulled, and there is no collision. Every ordinary build is quiet.
- **With** `runtime-symbol-table` — which `simple-native-all` enables — the
  archive is `--whole-archive`, so **every** C object is included whether needed
  or not, by design. The duplicates then collide.

So the double definition is a latent, tree-wide condition; `--whole-archive` is
only what makes it observable. The `--whole-archive` behaviour is not itself the
bug: the comment above states a real requirement (providers reachable only
through the generated symbol table would otherwise be dropped, leaving hosted
executables to abort in dyld before backend selection).

## Why no guard caught it — two guards, two different reasons

1. `check-seed-builds-push.shs` runs `cargo check`, which **does not link**. Its
   own header acknowledges that `check` "only skips codegen+link" and treats that
   as harmless; a duplicate symbol is invisible to it by construction.
2. `check-runtime-api-regression-push.shs` extracts the Rust `rt_*` set and the C
   `rt_*` set and evaluates them **separately, never unioned** — a deliberate
   choice, documented in that script, because unioning masked real Rust-only
   removals when a same-named C fallback still existed. That same choice makes it
   structurally incapable of noticing that both sides define the *same* name.

Neither guard is wrong on its own terms. The union of their scopes still has this
hole.

## Why this is not being fixed in this change

The C and Rust runtimes are **parallel implementations of the same names by
design** (stated in `.claude/rules/vcs.md` and in the API-regression guard's own
documentation). Deleting either side casually is exactly the failure mode that
guard exists to prevent. The genuine question is which definition the
`runtime-symbol-table` link is *intended* to bind:

- The **Rust** definitions are what the Rust crate's own callers bind to today,
  and `mem_snapshot.rs` is a first-class Rust module.
- The **C** definitions exist for the native/baremetal lane, where there is no
  Rust runtime at all — which is precisely the lane `simple-native-all` serves.

Establishing that intent requires evidence about the native lane that this
investigation does not have. Guessing risks silently binding the wrong
implementation of `rt_file_atomic_write` — a durability primitive — which would be
far worse than a loud link error.

## Suggested shape of a fix (unvalidated)

Precedent already exists in `runtime/build.rs` for compiling the C runtime
differently when the Rust side provides a symbol: `SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY`
and the `native_all_provider` flag both do exactly this. So the likely-correct fix
is a `#if`-gated exclusion of the four C definitions when the archive is being
built for a Rust-hosted link (a new define alongside the existing ones), leaving
the C definitions intact and active for the baremetal/native lane that has no
Rust runtime. That keeps both implementations and only decides, per link, which
one is in scope.

This is a hypothesis. It must be validated by actually linking `simple-native-all`
and by confirming the native/baremetal lane still resolves all four symbols.

## Actual root cause (measured 2026-08-17 — supersedes everything above)

The linker names both sides, and neither is C:

```
rust-lld: error: duplicate symbol: rt_file_atomic_write
>>> defined at simple_native_all.42a812a79b2b9b04-cgu.00
>>>            .../simple_native_all-243ad17baf575096.simple_native_all...cgu.00.rcgu.o:(rt_file_atomic_write)
>>> defined at simple_runtime.a13b17549e7407f2-cgu.02
>>>            simple_runtime...cgu.02.rcgu.o:(.text.rt_file_atomic_write+0x0) in archive .../libsimple_runtime.rlib
```

`libruntime_sffi_c.a` is on the command line under `-Wl,--whole-archive`, but it
supplies **none** of the four names — `runtime.c`, `runtime_legacy_core.c` and
`runtime_native.c` (the three C files holding those definitions) are not in
`build.rs`'s `c_sources` list at all, so they are not in that archive. The
`--whole-archive` mechanism section above is therefore a red herring.

The real conflict: `simple-native-all` defines all four itself
(`native_all/src/lib.rs:1166`, `native_all/src/mem_snapshot_provider.rs:225/271/397`)
and `runtime/Cargo.toml:23` already declares the feature that says so —
`native-all-provider = []  # simple-native-all owns overlapping aggregate exports`
— but that feature was **never read anywhere in `runtime/src/**`**, so the runtime
crate kept exporting them too.

## Resolution (applied)

Minimal edit, following the existing `driver-hooks` precedent
(`runtime/src/value/cli_sffi.rs:334`): gate the runtime's four exports on
`#[cfg(not(feature = "native-all-provider"))]` —
`runtime/src/mem_snapshot.rs` (4 items: both `rt_mem_snapshot_open` cfg-arms,
`_record`, `_close`, plus its `#[cfg(test)]` module) and
`runtime/src/value/sffi/file_io/file_ops.rs:365` plus its two tests. No C source
and no `build.rs` change; `--whole-archive` left exactly as it was.

Evidence — built at HEAD in an isolated `git worktree` (`/mnt/data/bugfix-wt-0dc81`)
because the shared working copy carries another lane's uncommitted, non-compiling
`module_loader.rs` edit (3x E0308) that blocks any build there:

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000

# BEFORE (HEAD, no fix): exit=101, all four duplicate-symbol errors reproduced.
$ CARGO_TARGET_DIR=/mnt/data/cargo-target-bugfix cargo test --release -p simple-native-all --no-run
$ rc=$?
exit=101

# AFTER:
$ CARGO_TARGET_DIR=/mnt/data/cargo-target-bugfix cargo test --release -p simple-native-all --no-run
$ rc=$?
exit=0
    Finished `release` profile [optimized] target(s) in 5m 18s
  Executable unittests src/lib.rs (.../release/deps/simple_native_all-243ad17baf575096)

$ /mnt/data/cargo-target-bugfix/release/deps/simple_native_all-243ad17baf575096
$ rc=$?
exit=0
test result: ok. 12 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 2.01s

# All four symbols are still exported by the linked binary (native_all's copies):
$ nm -D .../simple_native_all-243ad17baf575096 | grep -E ' T (rt_file_atomic_write|rt_mem_snapshot_(open|close|record))$'
00000000008a8a90 T rt_file_atomic_write
00000000008b6bd0 T rt_mem_snapshot_close
00000000008b6bf0 T rt_mem_snapshot_open
00000000008b7070 T rt_mem_snapshot_record

# Feature OFF paths unaffected — runtime's own tests still link, seed still checks:
$ cargo test --release -p simple-runtime --no-run   ; rc=0
$ cargo check --release --bin simple                ; rc=0
```

No `src/runtime/*.c` was modified, so `check-c-runtime-compiles-push.shs` was not
applicable and was not run.

## Exit criteria

1. `cargo test --release` in `src/compiler_rust` produces a linked
   `simple-native-all` test binary — quoted `test result:` line, rc read from a
   variable on the line after an unpiped invocation.
2. The baremetal/native lane still resolves all four symbols (it has no Rust
   runtime), demonstrated by a link, not by inspection.
3. A **collision** check added to `check-runtime-api-regression-push.shs` as a
   *third* check alongside its removal-count and still-re-exported checks: a name
   defined in both the Rust and C sets while the archive is `--whole-archive`.
   This is a new check, not a widening of the separate-sets design, so it does not
   reintroduce the masking problem that design avoids.
4. The link leg of `check-seed-builds-push.shs` promoted from advisory to gating
   once 1-3 hold.

**Status against these criteria (2026-08-17):** (1) MET — quoted above. (2) N/A
as written: the C definitions were never in this link, and none of them were
touched, so the baremetal/native lane is bit-for-bit unaffected by this change.
(3) NOT DONE — still open, and now needs a different shape than described: the
collision to detect is Rust-crate-vs-Rust-crate (`simple-runtime` vs
`simple-native-all`), which is outside `check-runtime-api-regression-push.shs`'s
Rust-set/C-set framing entirely. (4) NOT DONE.
