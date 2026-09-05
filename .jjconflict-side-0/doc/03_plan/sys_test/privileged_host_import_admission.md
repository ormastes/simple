# Privileged Host Import Admission System Test Plan

Status: **PROPOSED / RED**

No active `.spl` exists yet. Creating one before the HIR, MIR,
entry-closure, and interpreter hooks exist would either be unrunnable or test a
detached policy helper instead of the compiler boundary.

The spec freezes one compiler-owned metadata row without adding a runtime
provider. It must prove:

- only the canonical `ModuleSurface` owner is admitted for native compilation;
- declarations, imports, re-exports, and calls from another physical source
  fail before object emission;
- duplicate owner/requester objects fail entry-closure admission;
- the canonical owner is native-only in both interpreters;
- module-name, relative-path, symlink, copied-source, and
  `CURRENT_EXEC_MODULE` claims grant no authority; and
- ordinary hosted externs such as `rt_actor_recv` remain outside the
  privileged table.

The current RED is intentional: neither
`src/compiler/35.semantics/privileged_host_imports.spl` nor
`rt_browser_renderer_command_capability_new` exists on `origin/main`.
Implementation must add the compiler hooks before promoting this plan to an
executable SSpec. It must do so without using the Rust seed or a full
bootstrap.

## Frozen four-step manual

### 1. Compile the canonical privileged owner

- Native-build the hosted entry closure rooted at
  `src/os/hosted/hosted_entry.spl`.
- Confirm the requester for
  `rt_browser_renderer_command_capability_new` is exactly
  `src/os/hosted/hosted_browser_renderer_process.spl`.
- Confirm its object note records the same canonical physical identity.
- Confirm entry-closure admission finds exactly one requester object.

Expected result: compilation reaches normal runtime-provider settlement with
no `privileged-host-import-owner` diagnostic. Provider implementation is a
separate gate and may remain RED.

### 2. Reject a non-owner declaration

Native-build isolated hostile fixtures that:

- declare or call the raw symbol from a copied source;
- claim the owner's module name from another physical file;
- import and re-export the symbol from a facade;
- reach the owner through relative spelling and then add a second requester;
- present a symlink as a second source surface; and
- place both the canonical requester and a copied requester in one entry
  closure.

Expected result: every unauthorized requester fails
`privileged-host-import-owner` before object emission and before provider
lookup. A relative spelling is harmless only when it normalizes to the one
already admitted physical surface and creates no second requester.

### 3. Reject interpreter execution

- Force the exact canonical owner through the pure-Simple interpreter.
- Force it through the Rust interpreter.
- Repeat with `CURRENT_EXEC_MODULE` set to the owner-like module name.

Expected result: each attempt fails
`privileged-host-import-native-only` before builtin, local, static, or dynamic
lookup. Execution metadata never grants authority.

### 4. Preserve ordinary hosted externs

- Compile and interpret an existing ordinary hosted extern witness such as
  `rt_actor_recv`.
- Confirm it has no `PrivilegedHostImport` row.
- Confirm existing hosted lookup behavior remains unchanged.

Expected result: no privileged-owner or native-only diagnostic is emitted for
the ordinary hosted extern.

## Promotion gate

Add
`test/03_system/compiler/privileged_host_import_admission_spec.spl` and its
generated manual only after all compiler hooks named in the architecture
exist. The executable spec must use the four step titles above verbatim and
exercise real compiler entrypoints; policy-helper-only assertions are
insufficient.
