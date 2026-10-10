# cranelift-direct extern `text` cstr bridge breaks boxed-handle runtime ABI: `rt_file_write_text_at` returns -1 with zero syscalls (2026-10-10)

Status: OPEN (P1 — release-blocking for the strict bootstrap receipt chain;
call-site workaround landed in `fix/release-receipt-write-2026-10-10`)

## Symptom

The Stage-2-admitted pure-Simple compiler (cranelift-direct backend, dynload,
`core-c-bootstrap` runtime bundle) compiles
`src/app/cli/bootstrap_reason_planner.spl` fine, and the produced planner
binary accepts the typed reason and all four admission hashes, but exits 2:

    bootstrap-policy-error: receipt-write-failed: <receipt path>

`strace -f -e trace=openat,unlink,unlinkat,write,pwrite64` on the canonical
producer exec line shows `unlinkat(<path>) = -1 ENOENT` (the planner's
`rt_file_remove` of a not-yet-existing file) and then **no openat/fopen and no
write/pwrite for the receipt path at all**. `rt_file_write_text_at` returned -1
without issuing a single syscall.

## Measured root cause

Two ABI conventions exist for runtime entry points taking `text`:

1. **(ptr, len) two-word C ABI** — registered in
   `src/compiler/50.mir/text_extern_abi.spl` (`text_arg_indices`), mirrored in
   `src/compiler_rust/compiler/src/codegen/instr/calls.rs`. The compiler emits
   `rt_string_data` + `rt_string_len` per registered `text` arg. Example that
   WORKS in the same planner binary: `rt_file_remove` (registry row
   `Some([0])`; C ABI `rt_file_remove(path_ptr, path_len)`), proven by the
   observed `unlinkat`.
2. **boxed/tagged single-word handle ABI** — the generic one-word collapse,
   used by runtime impls that call `rt_core_string_to_cpath` /
   `tagged_text_to_str` on the argument (e.g.
   `src/runtime/runtime_native.c:14113`, `src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs:1405`).

`rt_file_write_text_at` belongs to convention 2, but it is **absent from
`text_arg_indices`**, so the cranelift-direct lowering applies its default
`text` extern bridge: each `text` arg is converted with `rt_interp_cstr`
(autodetecting tagged-or-raw) and the resulting **raw NUL-terminated pointer**
is passed as the single word. The strict-handle runtime then rejects the raw
cstr (`rt_core_as_string`/`tagged_text_to_str` fails on a non-tagged pointer)
and returns -1 before any libc call.

Disassembly evidence (planner binary from the 2026-10-10 qualification run,
admission dir under the isolated worktree `.simple/storage/build/bootstrap/admission/`):

    planner_file_write:
      bl rt_string_data; bl rt_string_len; bl rt_file_remove   # (ptr,len) split — OK
      bl rt_interp_cstr; bl rt_interp_cstr
      bl rt_file_write_text_at                                 # receives raw cstr — rejected

This is a compiler codegen defect (wrong bridge selection for strict-handle
externs), not a reachable-guard bug in the runtime: the identical call succeeds
when the runtime receives a real tagged handle (interpreter/seed path).

## Latent call sites (same defect, not fixed here)

Any natively-compiled (cranelift-direct) caller of a strict-handle
`rt_file_write_text_at` is silently broken the same way; interpreter callers
are fine. Known declarations:

- `src/lib/nogc_sync_mut/io/file_ops.spl:24` (`write_file_text`, line ~200) —
  used across std io in native builds.
- `src/lib/nogc_async_mut/io/mod_stub.spl:11`.
- `src/compiler/70.backend/backend/llvm_backend_tools.spl:27` (IR dumps; the
  return value is discarded at lines ~180/~375, so the failure is silent).
- `src/compiler/10.frontend/core/interpreter/eval_builtins.spl:19` —
  interpreter dispatch only; correct by construction.

## Fix applied (call-site workaround)

`src/app/cli/bootstrap_reason_planner.spl` now uses `rt_file_write_text`
(registry row `Some([0, 1])`, C ABI `(path_ptr, path_len, content_ptr,
content_len)`, `runtime_native.c:14230`, pure-Simple twin
`src/runtime/simple_core/core_fs.spl:520`) instead of
`rt_file_write_text_at`. `"wb"` create+truncate is exactly the planner's
remove-then-write-fresh-receipt semantics.

## Proper compiler fix (follow-up lane)

Teach the pure-Simple extern-call lowering to pass the tagged handle (no
`rt_interp_cstr`) for strict-handle runtime entry points. Options: extend the
registry with an explicit boxed-handle row set (negative of the (ptr,len)
table), or make the cranelift bridge consult a handle-ABI table mirroring the
runtime's `runtime_sffi.rs` specs. Must be reviewed against
doc/05_design/compiler/codegen/pure_simple_text_extern_abi_fix_plan.md §4.2/4.3
(lockstep with the Rust twin) — deliberately NOT done in the release fix lane.

## Evidence

- /tmp/beta-qual-evidence/planner.strace (zero write syscalls)
- /tmp/beta-qual-evidence/stage2.log (`planner-execution-nonzero-exit`)
- /tmp/beta-qual-4159b0b6/QUALIFICATION_EVIDENCE.md
