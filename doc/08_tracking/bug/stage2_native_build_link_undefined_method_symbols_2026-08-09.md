# Stage-2 native-build fails at LINK: 9 undefined symbols (unmangled Simple methods)

Date: 2026-08-09
Status: **OPEN — cause causally isolated to `36673b6b6a3` by a single-variable revert experiment.**
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

## Suggested fix direction

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
