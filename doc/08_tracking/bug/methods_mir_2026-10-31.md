# methods_mir_2026-10-31: unresolved method call (len/slice/substring/is_err) in MIR lowering

Found by: stage3 build (stage2 compiling `src/app/cli/bootstrap_main.spl`), 2026-10-31.
Error: `[mir-lower] WARNING: unresolved method call '<m>' is a FATAL lowering error (Task #145 ...)`.

## Root bug (compiler, not fixed here)
MIR method resolution only sees a receiver type when the HIR expression type reaches it as a
concrete type. These receiver shapes arrive untyped / unresolved:
1. untyped parameter (`fn f(value):`) used as `value[a:b]`, `value.substring(..)`, `value.len()`
2. result of a function with no declared return type (`fn g(v):` returning a list), then `.len()`
3. `text?` local after `if x == nil: return` (no flow narrowing in MIR) then `x.len()`
4. direct call-result receiver `f(x).is_err()` / `ctx.check_expr(..).is_err()`
5. unsafe-block value `val w = unsafe(...): rt_fn()` then `w.len()` (receiver_has_type=true, unknown kind)
6. enum-pattern payload bound array (`case Success(code, ..)` -> `code.len()`)

Pinned stage2 reproduces 1 and 2 directly (probe `build/probe/m1.spl`, lib serialization via
`build/probe/m2.spl`). Shapes 3-6 were NOT reproduced by a minimal probe or by importing
process_ops / sdn.parser into a probe (they failed only in the full stage3 closure); the
workarounds there add explicit annotations of the declared type, which is the known-good shape.

## Workaround sites (all tagged `# @workaround bug=methods-mir-20261031`)
- src/lib/common/serialization/__init__.spl: typed `value: text` params (is_numeric_text,
  parse_int_safe, detect_format, get_type_tag, strip_type_tag, get_version, strip_version,
  validate_field_type, escape_string, unescape_string, unquote_string, serialize_text_bytes,
  structural_hash_text, hex_to_bytes); `-> [i64]` on write_varint and serialize_text_bytes;
  `tag!` unwrap into `tag_text: text` in strip_type_tag.
- src/lib/nogc_sync_mut/io/process_ops.spl: explicit `[i64]`/`[u8]` on unsafe-block bindings
  (digest x2, words x3, limits, metadata x3).
- src/lib/common/sdn/parser.spl `_sdn_check_limits` Table arm: annotated rebinding of headers/rows.
- src/compiler/70.backend/linker/link.spl `case Success(code, ..)`: `code_bytes: [u8]`, `code_len`.
- src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl: `.is_err()` on annotated
  `Result<..>` locals (simpleos flags, elf runpath/hash-style/as-needed/gc-sections, coff flags).
- src/compiler/30.types/type_infer/typed_module_owner_v1.spl: `val checked = context.check_expr(..)`.
- NOT covered: `compiler.frontend.generated.ast_semantic_value` (generated file, one `len`
  with `<span-unavailable>`; site not identified, see report).

## Removal condition
Remove once the root fix (MIR receiver typing for shapes above) is in a stage2 used for bootstrapping.

## Status (2026-11-01 re-check)

**Status:** open (root bug present in current source; workarounds required).
Seed-hosted in-process pure-Simple HIR+MIR re-check
(`test/01_unit/compiler/50.mir/methods_mir_receiver_shapes_spec.spl`):
- Shapes 1-3 still fail closed with `unresolved method call` (shape 1: substring/slice; `.len()` on an untyped param now lowers).
- Shapes 4-6 lower clean in a single module (full-closure-only reproduction).
- The annotated workaround form lowers clean.

Design note (not attempted here, risky): shape 1 needs either a type-check error for
untyped params used with builtin methods or receiver typing from call-site
instantiation; shape 2 needs MIR to read the inferred return type of an un-annotated
function (30.types result) instead of only the declared type; shape 3 needs flow
narrowing of `T?` after an early-return nil guard to reach MIR's receiver type.
Revert-ready: no.
