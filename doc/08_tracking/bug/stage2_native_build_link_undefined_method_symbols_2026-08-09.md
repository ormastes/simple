# Stage-2 native-build fails at LINK: 9 undefined symbols (unmangled Simple methods)

Date: 2026-08-09
Status: **OPEN — the untyped last-resort intrinsic routing was reverted because
a leaf name does not prove a text receiver and can hijack unresolved custom
methods. The typed HIR/MIR repair covers the reproduced text calls; a clean
Stage-2 link remains the acceptance gate. Do NOT revert `36673b6b6a3`.**
Area: bootstrap / stage-2 native-build / Rust seed LLVM codegen (method dispatch symbol emission)

## Symptom

A full `--full-bootstrap` from a clean pinned `origin/main`
(`51115402161fdde06e253548cd8e264f1dd6ab44`) fails in Stage 2 at the **link**
step, exit 1, ~3 minutes in. No Stage-2 binary is produced, so Stage 3 and the
full CLI are unavailable and the run ends `exit-2`:

```
Build failed: link failed: /usr/bin/ld: .../mod_3.o: in function
  `app__cli__bootstrap_main___bootstrap_default_stem':
app__cli__bootstrap_main:(.text.simple.1+0x64): undefined reference to `rfind'
... undefined reference to `substring'
... undefined reference to `starts_with'
... undefined reference to `split'
... undefined reference to `replace'
... undefined reference to `char_code_at'
... undefined reference to `TaskState.is_terminal'
... undefined reference to `spl_mutex_lock' / `spl_mutex_unlock'
clang++: error: linker command failed with exit code 1
```

This failure is **fail-closed and fast** — no runaway log, no runaway RSS
(peak 2.6 GB for the whole process tree).

## The 9 undefined symbols split into two classes

| symbol | class | where it should come from |
|---|---|---|
| `starts_with`, `substring`, `rfind`, `split`, `replace`, `char_code_at` | **Simple `text` methods** | mangled Simple bodies (`lib__common__text__*`) |
| `TaskState.is_terminal` | **Simple enum method** | mangled Simple body |
| `spl_mutex_lock`, `spl_mutex_unlock` | C runtime externs | `src/runtime/runtime_thread.c:1161` |

Verified absent from every produced archive:

```
nm -g --defined-only target/bootstrap/{libsimple_runtime,libsimple_native_all,libsimple_compiler_backfill}.a
  -> 0 definitions for all of the above
```

The first two classes are the tell: these are **Simple methods emitted as
unmangled bare external calls**. `lib__common__text__contains` calls a bare
`char_code_at` rather than the mangled sibling in its own module. That is a
symbol-emission / method-dispatch defect in the seed's LLVM backend, not a
missing library.

## Causal isolation (single-variable experiment)

Suspect: `36673b6b6a3` *"fix(compiler): guard imported method dispatch and
arrays"* (landed 13:36 on 2026-08-09), which rewrote exactly the code that
chooses a call's target symbol:

```
src/compiler_rust/compiler/src/codegen/llvm/functions.rs        | 191 +++++++-------
src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs  | 110 ++++-----
src/compiler_rust/compiler/src/codegen/llvm/mod.rs              |  74 ++++++-
src/compiler_rust/compiler/src/codegen/llvm/emitter.rs          |  36 ++--
src/runtime/runtime_native.c                                    |  29 ++-
```

It landed **after** the last bootstrap that linked Stage 2 successfully
(`bfd9284618a`, 12:34-12:58, 126,202 KB binary), and before `origin/main`.

**Experiment.** Same checkout, same commit, same flags, revert *only* that
commit (`git revert --no-commit 36673b6b6a3`, applied cleanly; non-code files
restored to HEAD), rebuild everything:

| run | tree | Stage 2 result |
|---|---|---|
| 1 | pristine `51115402161` | **link FAILED**, 9 undefined refs, no binary |
| 2 | `51115402161` minus `36673b6b6a3` | **Linked OK — 809 compiled, 0 cached, 0 failed, 126,002 KB, 0 undefined refs**, sanity + capability gates passed |

Everything else held constant. `36673b6b6a3` is the cause.

## Why this matters beyond Stage 2

`origin/main` currently **cannot reach Stage 3 at all** — the self-host chain is
severed at the Stage-2 link. Any claim about Stage 3 behaviour on pristine
`origin/main` is presently untestable.

## Corrected root cause (2026-08-09, supersedes the revert experiment above)

The revert experiment is reproducible but its **conclusion was wrong**. Reverting
`36673b6b6a3` does not restore a working compiler — it restores a compiler that
**silently emits the same broken calls** and lets the linker bind them to
absolute address `0` instead of refusing them. The companion investigation
(`stage3_selfhost_segv_in_flat_ast_to_module_2026-08-09.md`) found 169 direct
`call 0` sites baked into the reverted binary; the "SIGSEGV in
`flat_ast_to_module`" was a **symbolization artifact** (gdb attributing address 0
to the nearest symbol, there being no frame info at 0).

So the two states are:

| tree | what happens to the bad call |
|---|---|
| with `36673b6b6a3` | undefined symbol → **link fails loudly, fail-closed** |
| without `36673b6b6a3` | binds to address `0` → **binary builds, then SIGSEGVs at runtime** |

`36673b6b6a3` is a correctness fix. The real defect is older and independent of
it: the seed's LLVM backend **mints an unmangled external for a call target it
could not resolve**, at the terminal fall-through in
`src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs`:

```rust
// last resort, after every get_function()/suffix-match strategy failed
module.add_function(&resolved_dotted, fn_type, None)
```

`resolved_dotted` here is a bare leaf (`char_code_at`, `substring`, `rfind`,
`split`, `replace`, `starts_with`) or a user-qualified name
(`TaskState.is_terminal`). Nothing defines those symbols, so the emitted call is
garbage by construction — the guard merely determines whether the garbage is
caught at link time or at runtime.

### Rejected fix: untyped terminal routing

Routing a terminal unresolved call by its leaf alone is unsafe: resolution
failure does not establish that the receiver is text. `UserText.replace`, for
example, must remain unresolved rather than silently becoming
`rt_string_replace`. Padding `substring(start)` to `rt_slice` is also wrong
without evaluating the receiver length. The rejected fallback and padding were
removed; canonical text calls must instead be selected while receiver type
information is still available in HIR/MIR.

### Historical measurement of the rejected fallback

Two commits from a parallel session landed on the same two files while this fix
was building — `3dfd2445d78` "harden text and mutex projections" (tightened
`resolved_text_runtime_method` to accept only the canonical
`lib__common__string_core__str` owner or a bare builtin owner) and
`f295b66d955` "link exact canonical mutex provider" (fixed the
`spl_mutex_lock`/`spl_mutex_unlock` build-composition gap). **They did not close
this defect.** The bare-leaf call targets (`starts_with`, `split`, …) have no
owner at all, and `resolved_text_runtime_method("replace")` returns `None` by
design, so nothing reaches them before the terminal fall-through.

Both trees built from scratch on the same host, same flags
(`bootstrap-from-scratch.sh --full-bootstrap --jobs=half`), differing only by
this fix:

| tree | Stage-2 link | undefined refs | binary |
|---|---|---|---|
| pristine `origin/main` `9bb19d8c913` | **FAILED** | **34** — `starts_with`×11, `split`×7, `replace`×7, `substring`×3, `rfind`×3, `char_code_at`×2 | none; "Stage 3 unavailable" |
| `9bb19d8c913` + this fix | **Linked OK** | **0** | 126,031 KB, 809 compiled / 0 cached / 0 failed, 232.3s |

The `#[cfg(test)]` regressions in `codegen/llvm/mod.rs` could **not** be executed
on this tree: `cargo test -p simple-compiler --lib` does not compile on pristine
`origin/main` `9bb19d8c913` either — 9 × `E0063: missing fields
struct_module_owners and unique_struct_owners`, all in
`pipeline/native_project/tests.rs` and `interpreter_call/block_execution.rs`,
none in any file touched here. That is a separate pre-existing breakage of the
lib-test target. The end-to-end Stage-2 link is the operative evidence.

With Stage 2 linking, **Stage 3 is reachable again for the first time** — it now
runs and fails with `exit 139` (SIGSEGV), which is the separate, pre-existing
self-host defect tracked in
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`, not a
regression from this fix. Before this fix Stage 3 could not be started at all.

`spl_mutex_lock`/`spl_mutex_unlock` and `TaskState.is_terminal` no longer appear
in either column — the mutex pair was fixed by `f295b66d955`, so the 36 of the
earlier run is now 34 and the residual-2 row below is closed.

### Measured result (earlier run on `5df72fefb49`, same host, same flags, only the fix differs)

| tree | Stage-2 link | undefined refs |
|---|---|---|
| pristine `origin/main` `5df72fefb49` | FAILED | **36** — `starts_with`×11, `replace`×7, `split`×7, `rfind`×3, `substring`×3, `char_code_at`×2, `spl_mutex_lock`×1, `spl_mutex_unlock`×1 |
| + this fix | FAILED | **2** — `spl_mutex_lock`, `spl_mutex_unlock` only |

All 34 references in the six `text`-method classes are gone; the log shrank from
8,886 to 987 bytes. The two survivors are the separate build-composition gap
below, and they are *supposed* to still fail until that lane is fixed.

Note the emission site was NOT the terminal fall-through in
`functions/calls.rs`: patching that one first produced a rebuild with the
**identical** 36 references, which is what isolated the real site in
`functions.rs`. Do not assume the two fall-throughs are interchangeable.

The last-resort table excluded some generic leaves but still admitted colliding
leaves such as `replace`, `split`, and `substring`; that is the same silent
miscompile class. Typed receiver-gated regressions now pin both directions.

The unsafe fallback-specific diagnostic was removed with the fallback; the
linker's undefined-symbol report remains the fail-closed evidence.

### Still open after this fix (as of the earlier `5df72fefb49` run — both now closed on `9bb19d8c913`)

- `TaskState.is_terminal` — a real Simple enum method whose **body is never
  emitted**. A resolution/emission gap, not an intrinsic gap. Correctly still
  fails the link.
- `spl_mutex_lock` / `spl_mutex_unlock` — **root cause now known**, and it is a
  build-composition gap, not a codegen gap. `spl_mutex_lock` is at
  `src/runtime/runtime_thread.c:1161` at preprocessor depth 0 (no `#if` encloses
  it — verified by nesting scan), so it is unconditionally compiled *if the file
  is compiled*. It is not: `src/compiler_rust/runtime/build.rs` — the crate that
  produces the `libsimple_runtime.a` the Stage-2 link consumes — lists
  **`runtime_pool.c`** and never `runtime_thread.c` (`grep -c runtime_thread.c
  build.rs` = 0), while `pipeline/native_project/tools.rs` lists
  `runtime_thread.c` and explicitly documents it as *"the canonical OS-thread
  and closure-pool provider … compiling runtime_pool.c beside it would create
  duplicate pool definitions."* The two lanes disagree, and only the
  `runtime_pool.c` lane feeds Stage 2 — and `runtime_pool.c` has no
  `spl_mutex_*` family at all (`nm` on the archive: zero `spl_mutex` symbols,
  defined or undefined).

  Beware the obvious probe: `spl_thread_cpu_count` IS in the archive and looks
  like proof that `runtime_thread.c` was compiled. It is not — that symbol is
  also defined in `runtime_legacy_core.c`
  (`scripts/check/runtime_bundle_duplicate_symbols_baseline.txt:126`). Probe with
  a symbol unique to `runtime_thread.c`, e.g. `spl_mutex_create`.

  This is the **third** instance of the same shape in this file's history:
  `runtime_contracts.c` was silently dropped from a source list by a `chore:
  sync` commit and broke the Stage-4 link on 2026-07-30 (see the comment at
  `tools.rs:290`), and the `rt_opengl_*` / `rt_sdl2_*` lanes before it. Not
  fixed here: reconciling the two lists is a runtime-lane change that must be
  landed against `scripts/check/check-runtime-symbol-lane-divergence.shs` and the
  duplicate-symbol baseline, not bolted onto a codegen fix.

Neither belongs in an untyped last-resort table. Each needs its own typed or
build-composition repair.

## Suggested fix direction (original, superseded)

Not fixed here (the defect is in the Rust seed's LLVM backend, and a blind
re-revert would discard whatever real bug `36673b6b6a3` was fixing). The right
move is to re-land `36673b6b6a3`'s intent with the imported/primitive-receiver
dispatch path still emitting the **mangled** callee, and to add a link-level
regression gate: after Stage 2 links, assert zero `undefined reference` lines,
which is a cheap fail-closed check the current wrapper does not perform.

## Reproduction

```
git archive 51115402161 | tar -x -C <work>   # + alternates + update-ref + read-tree
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=<outside repo> --progress
```

Logs: `logs/x86_64-unknown-linux-gnu/stage2-native-build.log` (8,160 bytes,
58 link-error lines).

---

## Acceptance gate MET — status line above is stale (W4 bug-fixing wave, 2026-08-17)

The Status header still reads OPEN with "a clean Stage-2 link remains the
acceptance gate", but the "Measured result" table in this same document records
that gate being met on `9bb19d8c913`: **Stage-2 linked OK, 0 undefined refs, 809
compiled / 0 cached / 0 failed, 126,031 KB, 232.3s**, with both stated residuals
(`spl_mutex_lock`/`spl_mutex_unlock` via `f295b66d955`, and
`TaskState.is_terminal`) closed. Nothing in this row is outstanding.

Fail-closed behaviour re-confirmed in current source: an unresolvable
`GlobalLoad`/`GlobalStore` target at
`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:3207-3225` returns
`CompileError::semantic("llvm global load referenced undeclared symbol ...")`
rather than minting a global. `36673b6b6a3` is intact — do not revert it.

**This row is the FIX for the family** whose other faces are
`stage3_native_build_sigsegv_call_to_zero_root_cause_2026-08-11` (169 `call 0`
sites measured per staged binary, 2026-08-17 — the pre-fix artifacts),
`bytespan_starts_with_dropped_from_kernel_closure_weak_nil_stub_2026-07-28`,
`freestanding_entry_module_constants_zero_stubs_2026-07-11`, and
`native_build_llvm_explicit_return_lost_every_call_returns_zero`.
