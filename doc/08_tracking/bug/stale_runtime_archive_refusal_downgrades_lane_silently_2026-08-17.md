# `native-build` prints "refusing to link a stale archive" and then links anyway (silent lane downgrade + default `--unresolved-symbols=ignore-all`)

- **Filed:** 2026-08-17 (lane STALELINK)
- **Severity:** P1 — silent wrong binary. Exit 0, no artifact-level diagnostic, produced binary segfaults.
- **Component:** Rust **seed** (`bin/simple` is the bootstrap seed; banner confirms). Path is
  `src/compiler_rust/compiler/src/pipeline/native_project/**` and
  `src/compiler_rust/common/src/platform/link_config.rs`.
- **Status:** FILED, not fixed. The fix is NOT small or certain — see "Why this was not fixed in place".

## Symptom

With `SIMPLE_NATIVE_BUILD_RUST=1`, `native-build` on a two-line hello-world:

1. emits `error: runtime archive is STALE: ... refusing to link a stale archive.`
2. **continues**, links, and exits **RC=0**
3. an unresolved symbol (observed: one literally named `fun`) is tolerated rather than failing the link
4. the produced binary **segfaults**

The word `error:` and the phrase "refusing to link" are both untrue: nothing is refused and
nothing returns an error.

## Root cause — three independent fail-open links in one chain

### 1. The refusal is a `continue`, not a return

`src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:639-649`

```rust
if let Some(stale) = stale_runtime_source(&path) {
    eprintln!("error: runtime archive is STALE: ... refusing to link a stale archive.", ...);
    continue;                     // <-- skips this candidate only
}
```

`find_simple_core_runtime_library()` returns `Option<PathBuf>`. When every candidate is stale it
returns `None`. There is **no error channel at all** — the function cannot report "stale" as
distinct from "absent". The in-source comment two lines above says "Fail loudly instead of
silently linking" — it fails *loudly* but not *closed*.

### 2. `None` is consumed as a lane-selection predicate, so staleness silently downgrades the lane

`src/compiler_rust/compiler/src/pipeline/native_project/config.rs:185-189`

```rust
if find_abi_complete_simple_core_runtime_library().is_some() {
    NativeRuntimeLane::SimpleCore
} else {
    NativeRuntimeLane::CoreCBootstrap      // <-- "stale" is read as "not available"
}
```

`resolve_runtime_lane()` returns a bare enum with no `Result`. A stale simple-core archive is
therefore indistinguishable from an absent one, and the build **quietly switches runtime lanes**.
That lane switch then rebuilds the core-C runtime from source (`config.rs:307-316`), which is the
~47.7s "link" time observed — the cost is a *symptom of the downgrade*, not of linking.

### 3. On Linux, unresolved symbols are ignored **by default**

`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1591-1596`

```rust
let strict_no_stub_fallback = std::env::var("SIMPLE_NO_STUB_FALLBACK").as_deref() == Ok("1");
if !strict_no_stub_fallback {
    for flag in &link_config.unresolved_symbol_flags { cmd.arg(flag); }
}
```

and `src/compiler_rust/common/src/platform/link_config.rs:83` (and `:146`):

```rust
unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition", "-Wl,--unresolved-symbols=ignore-all"],
```

**Default-on permissiveness.** Unless the caller sets `SIMPLE_NO_STUB_FALLBACK=1`, the link is run
with `--unresolved-symbols=ignore-all`, so any symbol the downgraded runtime lane fails to provide
links to nothing and traps at first call. macOS gets the equivalent
`-Wl,-undefined,dynamic_lookup` (`link_config.rs:107`).

Nuance worth recording: on Linux the missing symbol is **not** "stubbed" by
`generate_stub_object` — that call site (`linker.rs:1578-1589`) is `#[cfg(target_os = "windows")]`.
On Linux the equivalent effect is produced purely by the linker flag above. The user-visible
outcome is identical (segfault), the mechanism is not.

### Is stubbing default-on?

Yes, in the sense that matters: every stub/unresolved escape hatch in this pipeline is
**opt-out**, keyed on `SIMPLE_NO_STUB_FALLBACK=1`:

| site | default when env unset |
|---|---|
| `linker.rs:1592` | passes `--unresolved-symbols=ignore-all` |
| `stubs.rs:110-132` `freestanding_unresolved_mode()` | `DeferToLinker` (i.e. defers to the permissive linker above) |
| `stubs.rs:994`, `linker.rs:1102` | strict checks disabled |

The one genuinely fail-closed sibling is `SIMPLE_ALLOW_STUB_FALLBACK` in
`src/compiler_rust/compiler/src/codegen/common_backend.rs:2172` — that one is **opt-in** and errors
by default with the correct wording ("unsafe — binary will silently misbehave"). The linker-side
knobs should follow that polarity and do not.

## Why this was not fixed in place

Each of the three links is a policy change with wide blast radius, not a typo:

- Fixing (1)+(2) properly means giving `find_simple_core_runtime_library` a
  `Result<Option<_>, StaleArchive>` and threading it through `resolve_runtime_lane()`, which today
  returns a bare enum and is called from several sites. Making staleness fatal at (1) alone would
  break any lane that legitimately expects the CoreCBootstrap fallback.
- Fixing (3) by flipping `--unresolved-symbols=ignore-all` to off-by-default would change every
  freestanding/OS/bootstrap link in the tree at once. `.claude/rules/bootstrap.md` documents lanes
  that are only expected to pass *with* `SIMPLE_NO_STUB_FALLBACK=1` set explicitly, which implies
  the unset default is load-bearing for others today.

Half-fixing a linker path is worse than filing it, so it is filed.

## Recommended fix (in order)

1. **Make staleness a distinct, propagated outcome.** `find_simple_core_runtime_library` should
   return a three-state result (`Found` / `Absent` / `Stale{..}`); `resolve_runtime_lane` returns
   `Result<NativeRuntimeLane, String>` and errors on `Stale` rather than downgrading. A stale
   archive is a *broken* configuration, not a *missing* one.
2. **Better still, rebuild it.** `build_core_c_runtime_library` already exists and is invoked on
   the CoreCBootstrap path; the SimpleCore path has no equivalent. A stale simple-core archive
   with sources present should trigger a rebuild, exactly as `config.rs:369-386` insists a
   failed core-C build in a source checkout is "a toolchain defect, not a supported configuration".
3. **Invert the linker default.** `--unresolved-symbols=ignore-all` should be opt-**in**
   (`SIMPLE_ALLOW_UNRESOLVED_SYMBOLS=1`), matching `SIMPLE_ALLOW_STUB_FALLBACK`'s polarity in
   `common_backend.rs:2172`. This needs a tree-wide sweep of the freestanding lanes first.
4. Regardless of the above: **a build that printed a line starting `error:` must not exit 0.**
   A cheap, independently valuable guard is an error-counter checked before the success return.

## Reproducer

Precondition (present on this host): the simple-core archive is older than the runtime sources.

```
$ ls -l build/simple-core/libsimple_runtime.a   # Aug 17 22:09
$ ls -lt src/runtime/*.c src/runtime/*.h | head -1  # runtime_fork.c  Aug 18 00:07
```

```sh
printf 'fun main()\n    print("hello")\n' > /tmp/hello.spl
SIMPLE_NATIVE_BUILD_RUST=1 bin/simple native-build /tmp/hello.spl -o /tmp/hello.bin
echo $?          # rc on its own line, never through a pipe
/tmp/hello.bin; echo $?
```

Expect: the STALE `error:` line, then rc=0, then a segfault (139) from the binary.

## Reproduction status on this host: NOT REPRODUCED (inconclusive — earlyoom, not a failure)

Attempted 2026-08-17/18 by lane STALELINK. **The run did not complete and must not be read as
either a confirmation or a refutation.**

- The invocation *was* on the intended route: `SIMPLE_NATIVE_BUILD_RUST=1` is honoured at
  `src/compiler_rust/driver/src/main.rs:168-172`, which dispatches straight to the Rust handler.
- The process (PID 1633022) ran 5+ minutes under host load-avg 85, RSS climbing 60 MB -> 635 MB,
  and was then **SIGTERM'd**. The shell reported `Terminated`.
- This was **earlyoom, not a build failure**. `journalctl -t earlyoom` for the same window shows
  `mem avail: 12854 of 128683 MiB (9.99%) ... low memory! ... sending SIGTERM to process ... "simple"
  badness 1013, VmRSS 9027 MiB`. Host had ~1 GB free with ~15 concurrent lanes building.
- Consistent with an external kill rather than native-build's own timer: **no
  `[TIMEOUT: Process killed after Ns]` line was emitted**, which native-build prints when its own
  timer fires. Per lane convention an rc of 143/144 is UNVERIFIED, never "failed".
- Only the seed banner reached `build.log`; the STALE line was never reached, and **no binary was
  produced**, so the segfault half could not be tested either.

### Measurement error worth recording (the defect's own failure mode, in the harness)

The rc was captured as `... ; echo "RC_LINE"; echo $?`. That reads the exit status of the
intervening `echo`, **not** of `native-build` — it printed a meaningless `0`. Had it been trusted,
this file would have claimed "rc=0" as evidence for a bug that is *about* a bogus rc=0. Capture rc
into a variable on the line immediately after the command, exactly as
`check-c-runtime-compiles-push.shs` does, and never let another command intervene.

Re-running was declined rather than retried: the host was at ~1 GB free with earlyoom actively
killing `simple` processes, so another attempt would have harmed concurrent lanes without a
better chance of completing. **The static analysis above stands on its own and does not depend on
this reproduction**; the three code paths are read directly from committed source. A repro should
be re-attempted on an idle host.
