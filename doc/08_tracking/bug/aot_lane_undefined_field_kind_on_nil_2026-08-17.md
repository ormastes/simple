# AOT lane broken: `undefined field 'kind'` on a nil driver-manifest, then ENAMETOOLONG cache scope

- **Date:** 2026-08-17
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Status:** FIXED (both defects), verified by the smoke gate
- **Severity:** HIGH — `native-build` could not produce a binary for *any*
  program, blocking every AOT-dependent lane (draw_ir 8K, gui 8K, fat32).

## Symptom

```
$ sh scripts/check/check-aot-smoke.shs
binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
FAIL — AOT lane broken: native-build exit 1, binary absent
```

with, in the worker stderr:

```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
```

## Full error, with the site

The one-line summary carries no location. `SIMPLE_DEBUG_FIELD_ACCESS=1`
(handled in `src/compiler_rust/compiler/src/interpreter/expr/calls.rs:977`)
yields the receiver and the call stack:

```
[field-access-error] field=kind recv_type=nil recv=nil
  expr=FieldAccess { receiver: Identifier("function"), field: "driver_manifest_attr" }
  stack=main -> cli_native_build -> compiler_driver_run_compile -> compile -> aot_compile
        -> compile_to_native -> freeze_native_module_capsules_v1
        -> native_capsule_mir_identity_v1 -> native_capsule_function_metadata_identity_v1
```

Repro (any program at all, the smoke probe is a 2-field struct):

```
SIMPLE_DEBUG_FIELD_ACCESS=1 bin/simple native-build probe.spl -o probe_bin
```

## Causation verdict: COMMITTED, and present verbatim at `origin/main`

The prior hypothesis — that the ~13k uncommitted lines under
`src/compiler_rust/**` from parallel sessions were responsible — is **refuted**:

- `bin/simple` is a *prebuilt* binary. Uncommitted Rust source is not compiled
  at run time and cannot affect this run unless the binary is rebuilt from it.
- The faulting code is **pure-Simple**, read as source on every run.
  `git status --porcelain -- src/compiler src/lib | grep '\.spl'` reports
  exactly **one** modified file
  (`src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl`), unrelated to
  native-build.
- `git show origin/main:src/compiler/80.driver/driver_types.spl` contains the
  faulting line at the identical line number 276, and `git diff HEAD` on that
  file was empty. Introduced by the native-capsule storage series
  (`ee1316c53f5` / `e1625f702fd`).

So this was **committed state**, already at origin — not cross-session
in-flight work, and no coordination handoff is needed.

## Root cause 1 — unguarded nil deref

`src/compiler/80.driver/driver_types.spl:276`

```
val manifest_kind = match function.driver_manifest_attr.kind:
```

`driver_manifest_attr` holds the `DriverManifestAttr?` produced by
`parse_driver_manifest_attrs`, stored straight through at
`src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:549-550`,
and is **nil whenever `has_driver_manifest_attr` is false** — that is, for
every function that carries no `@driver`/`@native_lib` attribute, i.e. nearly
all of them. `src/compiler/60.mir_opt/mir_opt/outline.spl:430-431` likewise
constructs `has_driver_manifest_attr: false, driver_manifest_attr: nil`.

This is the same defect class already documented in the long comment at
`declaration_lowering.spl:502-515` (the 2026-08-01 SIGILL/exit-132 incident);
the new capsule-identity code reintroduced the unguarded dereference at a new
site.

**Fix:** guard all six `driver_manifest_attr` reads on
`function.has_driver_manifest_attr`, defaulting `manifest_kind` to `"none"`.

## Root cause 2 — cache scope exceeds NAME_MAX (uncovered by fixing #1)

With #1 fixed, native-build reached codegen and failed differently:

```
error: Failed to write object file build/native_cache/lane=default;backend=llvm;...;bundle=-storage-<sha256>/sources-.../object.probe.o:
       Failed to write ELF bytes to ...
```

The scope is a **single directory component**, built in
`src/compiler/80.driver/driver_aot_native_output.spl:81-93`. Appending
`"-storage-" + sha256_text(storage_identity)` (64 hex chars) to `compiler_id`
took that component to **295 characters**, over the POSIX `NAME_MAX` of 255.
Confirmed directly: `ls -d 'build/native_cache/<scope>'` →
`File name too long`. The driver reported this only as a generic write
failure.

**Fix:** when the component would exceed 200 chars, keep a readable 160-char
head and append `;digest=<sha256 of the full key>`, preserving injectivity.

## Verification

```
$ sh scripts/check/check-aot-smoke.shs
binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
PASS — 1 probe checked (built, ran, struct copy + f64 field formatting verified: a.n=7 b.n=99 a.x=1.5)
```

## Follow-ups (not done here)

- Neither defect is reachable from the spec corpus: specs run
  interpreter/JIT only, so `freeze_native_module_capsules_v1` is never
  executed. `check-aot-smoke.shs` remains the only gate that would have caught
  either. A reproducing/prevention SSpec pair needs an AOT-capable harness;
  filed as a follow-up rather than faked with a JIT-only spec.
- Root cause 2 is latent for **any** future addition to the scope key. A
  NAME_MAX assertion in `native_build_cache_scope_key`
  (`src/compiler/80.driver/driver_build/incremental.spl:207`) would turn the
  next occurrence into a clear error instead of an opaque write failure.
