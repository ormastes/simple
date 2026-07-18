# Bug: erased-receiver `.len()` emits bare `MethodCallStatic("len")` → links to arbitrary `_dot_len` symbol (entry-closure)

- **Status:** FIXED — `610b4572a32` (2026-07-16)
- **True root cause (superseding the hypothesis below):** the `?` Try operator
  never reached the parser. Under `SIMPLE_BOOTSTRAP=1`,
  `apply_bootstrap_rewrite()` (`pipeline/native_project/compiler.rs`) blindly
  stripped any `?`+terminator pattern (meant for `Type?` optional suffixes),
  silently deleting `val resp = _vfs_request(...)?`'s Try — `resp` stayed the
  raw `Result<text,text>` wrapper, `resp.len()` qualified as the nonexistent
  `Result.len`, and suffix-based symbol resolution bound it to
  `BinaryWriter.len`. Fix: byte-safe scanner that never strips `?` preceded by
  `)`, plus defense-in-depth in MIR (Result/Option-wrapper receivers with
  builtin-collision names route through erased-builtin tag dispatch) and
  `is_empty` added to `is_bare_builtin_collection_method`. Verified: exception
  frames 2→0; boot proceeds through pkg_service to the separate fb-init
  regression. Residual risk noted: bare-variable Try (`resp?` with no `)`)
  would still be stripped by the rewrite — none exist in the kernel closure
  today.
- **Residual-risk audit (2026-07-17):** repo-wide scan found 915 line-end `?`
  occurrences, ALL type annotations/comments/`.?` chains — ZERO bare-variable
  Try operators in any closure (kernel, bootstrap_main, GUI entries). Blast
  radius zero. Extending the protection set is provably unsafe by character
  inspection alone (`dict[k]?` vs `[T]?` both end `]?`) — requires
  context-aware detection; file a feature request if bare-Try is ever needed
  under SIMPLE_BOOTSTRAP. No code change made.
- **Date:** 2026-07-16
- **Severity:** critical (SimpleOS x86_64: fat32 `exec probe failed` → `mount_failed` → diskless desktop)
- **Component:** rust seed — HIR `?`-unwrap type propagation + MIR dynamic method dispatch
- **Related:** `simpleos_native_build_bare_ok_err_canonicalization_skipped_2026-07-16.md` (sibling family: erased builtin routing under `--entry-closure`); NOT the field-index bug (`..._crossmodule_field_offset_shift_2026-07-14.md` — that patch guards `FieldAccess` only, this is `MethodCall`)

## Symptom
Recovered faults `cr2=0x1800000008, rip=0x126cd5` in
`lib__common__binary_io__BinaryWriter_dot_len` during `pkg_service_init()` →
`PkgManager.load()` → `_load_installed_db()` → `readdir("/pkg/installed")`;
downstream `exec probe failed` → `[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs`.
Evidence: `build/os/_wk/serial2.log` + `nm`/`objdump` on `build/os/_wk/desktop.elf`.

## Mechanism (proven read-only from the binary)
Faulting source: `src/os/userlib/fs.spl:71` — `if resp.len() == 0:` where
`val resp = _vfs_request(VFS_READDIR, path)?` and `_vfs_request` returns
`Result<text, text>`.

1. Under `--entry-closure`, the `?`-unwrap of `Result<text,text>` loses the
   payload type: `resp` lowers as `TypeId::ANY` instead of `TypeId::STRING`.
2. In `hir/lower/expr/mod.rs`, `is_string`/`is_array` are false for ANY →
   `is_any` branch → `DispatchMode::Dynamic`.
3. In `mir/lower/lowering_expr_method.rs` (~560–579), with no vtable/trait
   match and no qualifiable type name, `func_name` stays the bare unqualified
   `"len"`, emitted as `MethodCallStatic`.
4. The backend/linker binds bare `len` to whatever `_dot_len` symbol is linked —
   here `BinaryWriter.len` (`mov rax,[rdi+8]` after untagging `self.buffer`),
   whose field read on a text value dereferences a tagged garbage pointer.
   Confirmed: the ONLY call site targeting 0x126b28 in the 42MB kernel is
   `os__userlib__fs__readdir`, passing the raw `_vfs_request` return register.

## Fix direction (compiler-level; no OS-source rewrites)
1. **Preferred/root:** fix `?`-operator HIR payload-type propagation so
   `Result<text,text>` unwraps keep `TypeId::STRING` under `--entry-closure`
   (same gap class as the fixed Result/Option static-member routing,
   `86e56ca7867`).
2. **Defense-in-depth (apply regardless):** in the `DispatchMode::Dynamic`
   branch of `lowering_expr_method.rs`, never emit a bare/unqualified builtin-
   colliding method name (`len`, `is_empty`, `contains`, …) as
   `MethodCallStatic` when the receiver can't be statically qualified — route
   through a runtime tag-dispatching helper (mirror the existing
   `receiver_is_array` → `rt_array_len` special case at ~line 260, extended to
   strings/dicts), so an unqualified name can never link to an arbitrary
   same-named user struct method.

Verify with full clean kernel build + QEMU boot: BinaryWriter.len faults gone,
`exec probe` passes, fat32 mounts with apps > 0. Mirror in self-hosted compiler
(`src/compiler/50.mir/`).
