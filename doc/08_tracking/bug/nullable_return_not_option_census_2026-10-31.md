# Nullable return not declared Option: census (2026-10-31)

Rule: anything that can return nil declares `T?`; a function typed `T` never returns nil.
Scope: src/lib, src/app, src/os, src/compiler (17,255 .spl, vendor/generated excluded).
Single-line signatures only; multi-line signatures are not seen by any count below.

## Existing enforcement (found, extended)
- Runtime: `validate_sffi_return_contract` (compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:93)
  raises `nil is forbidden by the non-optional return contract of '<fn>'` [E-SFFI-016]. It only fires
  when the nil path EXECUTES, in the interpreter. It misses: unexecuted nil paths, extern calls whose
  provider returns nil under a non-optional extern decl (the nil flows into the wrapper and trips there,
  attributed to the wrapper), and native codegen.
- Lint: no rule in src/compiler/90.tools/lint or 35.semantics checks this. Earlier sweep 3bfd830c898 +
  test/01_unit/app/contract/app_non_optional_nil_return_spec.spl covered src/app only (this tree predates it).
- New: scripts/check/check-nullable-return-option-ratchet.shs (+ baseline).

## Class a: `-> T` fn with `return nil` / trailing `nil`
Raw 24 (awk). Validated by reading each: 4 false positives (`Option<fn() -> i64>`, `(i64, text)? :`
spaced `?`, `fn(T) -> bool` param arrows, no declared return). Real ~20; fixed 4 here
(AgentSessionRegistry.session/event_at, AdapterRegistry.find_by_kind/find_for_meta; callers already use `.?`).
Remaining baselined (17 entries, includes 2-3 known FPs: thread_pool get_value_task_callback, ccrClient flushInternalEvents unverified):
dwarf.spl x3 (app) + lib dwarf load, breakpoint_manager.get_breakpoint, assistant_session_by_id,
_group_active_buffer, hir_codec_support x5, hygiene.resolve, type_subst.substitute_param_node_v1,
runtime_compiler.c_compiler_override. Callers NOT audited; left for per-owner fixes.

## Class b: non-optional `extern fn rt_*` whose interpreter provider returns nil
Raw 15 names (163 provider fns with Value::Nil x 2,603 distinct non-optional decls). Validated 5 real families
(provider returns nil on error): rt_file_read_text (83 non-opt decl sites vs 11 opt), rt_file_read_bytes (20/17),
rt_file_read_lines (1/2), rt_dir_list (13/2), rt_file_hash_sha256 (14/0). The rest were unit/i64 sentinels or `auto` (FP).
Fixed: file_ops.spl rt_file_hash_sha256 -> `text?`, `file_hash_sha256` total with "" default (callers compare
digests; "" fails closed). NOT fixed: ~131 decl sites duplicated per-file (each app re-declares the extern);
changing them needs per-caller nil handling; sibling decls in sffi/io.spl, io_runtime.spl, both mod_stub.spl still `text`.

## Class c: same-named fns disagreeing `T` vs `T?`
Raw 33 names (single-line sigs, same base type). Mostly private helpers in different modules (benign).
Real hazards: `env_get` (10 text vs 4 text?: compiler/00.common/config, 90.tools/header_gen/shared_lib_flags,
gc_async_mut/env/variables, nogc_sync_mut/src/config), `file_read_text` (3 text vs gc_async_mut/file_system/file_ops text?),
`is_directory`, `parent_dir`. env_get `text` variants are documented total (""); not changed.
