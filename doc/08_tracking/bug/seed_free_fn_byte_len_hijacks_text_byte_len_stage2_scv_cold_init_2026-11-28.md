# Seed-built Stage 2: a free `fn byte_len` in the closure hijacks every `text.byte_len()`

Status: source workaround landed (rename + reason-bearing refusal), verified on
reduced native probes built by the pinned `c6e3ee3c112` seed. NOT yet confirmed
by a full Stage 2 bootstrap. The seed mangler defect is FIXED in source (see
"Seed fix" below) and verified on a two-module native reproducer; the
`lb_byte_len` workaround stays until a Stage 2 rebuild with the fixed seed
confirms it.

- **Severity:** P1 (every aarch64 Stage 2 candidate refused cold SCV admission)
- **Area:** Rust seed native-project mangler; `src/os/kernel/loader/byte_utils.spl`
- **Workaround site:** `src/os/kernel/loader/byte_utils.spl` (`lb_byte_len`, tagged `# @workaround bug=...`)
- **Shard:** `doc/08_tracking/bug/db/seed_free_fn_byte_len_hijacks_text_byte_len_stage2_scv_cold_init_2026-11-28.sdn`
- **Spec:** `test/01_unit/app/compiler_entrypoint/inventory_refusal_reason_spec.spl`

## Symptom

`--full-bootstrap --stop-after-stage2` pinned at `c6e3ee3c112` (aarch64) aborted
at Stage 2 sanity with `candidate_frontend_smoke: scv-prime-inventory failed
(raw rc=1)`. The `.scv-prime` log held only:

```
[coordinator-route] per-file worker pool + per-module link
[scv] cold-init scan start lines=102871
SCV-E-ADMISSION: git-event-refresh-failed
```

Pins at `f3cf72db429` and `f43f68c218e` passed the same step.

## Root cause

Two causes, and only the second is in the regression range.

1. **Latent seed defect (predates the range).** The seed-built binary calls a
   free user `byte_len` for a text `x.byte_len()` in a module that never
   imports it. The rebinding site inside the seed was NOT isolated (see Open).
   `src/os/kernel/loader/byte_utils.spl` declared the only free
   `fn byte_len(data: [u8])` in the tree, so once that module is in a closure
   every `x.byte_len()` on a text in the WHOLE closure is rebound to it. The
   module that calls it does not have to import it.
2. **Trigger: `bf0dc71aaf8` (PR #12182, W5-2).** It wired
   `app.cli.bootstrap_driver_provider_client_v1` into
   `src/app/cli/bootstrap_main.spl`. That import reaches `os.smf.provider_loader`
   -> `os.posix.dynlib` -> `os.posix.dylib_async` ->
   `os.kernel.loader.dylib_registry` -> `elf_loader` / `smf` -> `byte_utils`.

On arm64 the hijacking body is `rt_arm_array_len_u32(data)`, which reads 0 for
a text. `line.byte_len() <= 2` in the cold-init row walk
(`src/app/compiler_entrypoint/inventory_events.spl`) then refused the first row
(`H examples/10_tooling/README.md`). On x86_64 the body is `data.len()`, which
happens to be right for ASCII text, so the defect is silent there.

## Evidence (2026-11-28, aarch64)

- Rerunning the scv-prime command with the pinned `c6e3` candidate in a fresh
  `c6e3` worktree reproduces in 0.5 s; the `f3cf` candidate on the same tree
  scans normally. Binary, not tree.
- `objdump` of `..._compiler_inventory_git_events_traced_cost_v1` in the `c6e3`
  candidate calls `os__kernel__loader__byte_utils__byte_len`; the `f3cf`
  candidate does not. The `c6e3` candidate has 1028 call sites of that symbol
  and 42 `os__*` text symbols; the `f3cf` candidate has none.
- gdb: `_compiler_inventory_event_for_path_cost_v1` is never entered, so the
  refusal is the row-shape check on row 1.
- Direct probe (both seeds, `native-build --backend llvm`): with
  `use os.kernel.loader.byte_utils.{lb_read_u8}` in the file,
  `"H examples/10_tooling/README.md".byte_len()` prints 0. The `f3cf` seed
  prints 0 too, which is what makes cause 1 pre-existing.
- Scope probe (pinned `c6e3` seed, fixed tree): an entry file that declares its
  own `fn byte_len(data: [u8]) -> i64: 0` and calls the cold-init refresh.
  The entry module itself still reads `byte_len=31`; `inventory_events.spl`,
  which does not import it, is hijacked and refuses with
  `git-event-refresh-failed:row-shape:byte_len=0:H examples/10_tooling/README.md`.
  So one free `byte_len` anywhere in the closure is enough, and the new reason
  text is what a compiled candidate prints.
- Chain probe (pinned `c6e3` seed, entry importing the provider client and
  calling `compiler_inventory_refresh_v1(.., cold_init = true)`):
  pre-fix tree prints `byte_len=0` and `reason=[git-event-refresh-failed]`;
  the fixed tree prints `byte_len=31` and publishes the inventory.

## Fix

- `byte_len` in `byte_utils.spl` is renamed `lb_byte_len` (all six `@cfg`
  variants, its two internal callers, `fs_exec_spawn.spl`, and
  `test/01_unit/os/kernel/loader/byte_utils_spec.spl`). No free `byte_len`
  remains in the tree, so the seed has no candidate to bind.
- The refusal names its reason. `_compiler_inventory_git_events_traced_cost_v1`
  returns `Result<CompilerInventoryGitEventsV1, text>`, and the admission error
  becomes `git-event-refresh-failed:<branch>:<detail>`; the row-shape reason
  carries the measured byte length (`row-shape:byte_len=0:H examples/...`), so
  this class is self-evident the next time it happens.

## Seed fix (2026-11-28)

Rebinding site isolated by instrumenting the mangler on a two-module
reproducer (a free `fn byte_len(data: [u8]) -> i64: 99` in `util/bytes.spl`; a
second module that does not import it calls `s.byte_len()` on a text):

- `s.byte_len()` reaches the mangler as `MirInst::MethodCallStatic` named
  `str.byte_len`, not as a bare name and not as a `Call`.
- Nothing binds it until the "text UFCS" arm at the end of
  `resolve_method_call_static`
  (`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`): for a
  `str` / `text` / `string` qualifier it takes the LONE unowned candidate for
  the leaf in the closure-wide suffix index. That index does not know what the
  calling module imported and carries no parameter types, so one free
  `byte_len` in the closure captures every text `.byte_len()`.
- This is the LLVM lane. The Cranelift backend does not run `mangle.rs` and
  gets every typed shape right; it has its own, narrower instance (see Open).

Seeds built from `bf9f1968949` with `--features llvm`, host aarch64. The
second probe adds an optional unwrap, a struct text field, a cross-module call
result, a dict value, a field in a struct loop, an untyped parameter and a
free `char_count` in the closure (wanted `3 7 6 4 5 9 3`):

| seed | backend | first probe | second probe |
|---|---|---|---|
| unfixed | llvm | `99 99 198 99 99` | `99 99 99 99 198 99 55` |
| unfixed | cranelift | `5 5 5 4 99` | `3 7 6 4 5 99 3` |
| fixed | llvm | `5 5 5 4 99` | `3 7 6 4 5 9 3` |
| fixed | cranelift | `5 5 5 4 99` | `3 7 6 4 5 99 3` |

The JIT (`simple main.spl`) prints the Cranelift rows.

Fix: `is_text_builtin_method_call` in `mangle.rs`, for method-syntax calls
named `byte_len` / `char_count`:

- under a `str` / `text` / `String` / `string` qualifier the call is never
  rebound; it stays as emitted and the LLVM lowering sends it to
  `rt_string_len` / `rt_string_char_count`;
- bare (erased receiver) it is no longer bound by a closure-wide arm: the bare
  project import-map entry in `mangle_mir`'s `MethodCallStatic` arm, and the
  name-variant, lone-suffix-candidate and `resolve_unbound_by_suffix` arms of
  `resolve_method_call_static`.

Still bound, as before: a function the module defines or names in a `use`, a
`byte_len` method of a type the module imports, and a free call
`byte_len(data)` (a `Call`, which legitimately resolves closure-wide). Pinned
by `closure_wide_free_fn_never_captures_text_builtin_method_calls` (red with
the guard disabled, green with it).

## Open

- The seed fix is not yet exercised by a Stage 2 bootstrap. Remove the
  `lb_byte_len` `@workaround` only after a `--full-bootstrap
  --stop-after-stage2` run on the fixed seed passes.
- Cranelift / JIT, not fixed here: `fn f(x): x.byte_len()` with an UNTYPED
  parameter holding a text calls the closure's free `byte_len` (prints 99,
  both seeds). That lane resolves in `codegen/instr/calls.rs` through
  `ctx.import_map`, not `mangle.rs`. Typed receivers are correct there.
- Residual, by construction: the mangler has no receiver types. A bare
  (erased-receiver) `.byte_len()` in a module that defines or imports a free
  `byte_len` still binds to that function (measured: an untyped parameter
  holding a `ByteBuf` in a module importing both prints the free function's
  99, same on both seeds). Other text builtins with a codegen lowering
  (`split`, `replace`, `substring`, `rfind`, `bytes`) keep the lone-candidate
  text-UFCS arm and have the same exposure if the closure ever holds exactly
  one free function of that name.
- `byte_utils.spl` also declares a free `byte_at`. The `c6e3` candidate carries
  no `byte_utils__byte_at` symbol, so it is not hijacked today. A probe with a
  lone free `byte_at(data: [u8], i)` in the closure left `"hello".byte_at(1)`
  correct (101) on the unfixed LLVM seed, so the seed fix does not touch it.
- A full `--full-bootstrap --stop-after-stage2` run is still needed to prove the
  Stage 2 gate passes.
