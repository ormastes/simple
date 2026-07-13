# Interpreter Shared Text Compile WIP

## Status

Non-buildable WIP retained by higher review. Do not fold or independently fix
the owned files listed in
`doc/03_plan/design/interpreter_shared_text_owned_files.txt`.

## Bounded Compile Evidence

- Cycle 1 after coherent `Value::Str(Arc<String>)` flip: 614 errors.
- Compiler-assisted/mechanical constructor conversion applied.
- Cycle 3: 217 errors; mandatory cap reached.
- Authoritative command: `cargo check -p simple-compiler --message-format short`
  from `src/compiler_rust`.

## Remaining Groups

1. Constructor variables and complex/multiline `Value::Str` expressions.
2. True owned-`String` extraction boundaries and accessors.
3. `Arc<String>` arguments to string pattern APIs.
4. BDD/mock match-arm ownership normalization.
5. OS/FFI `AsRef<OsStr>` boundaries.
6. `Vec<Arc<String>>` to `Vec<String>` conversions.
7. Unicode collection/slice outputs and type inference.

Next continuation gets at most three new grouped compile/fix cycles. Start with
shared conversion owners (`Value::text/shared_text`, owned-string accessors,
and vector conversion helpers), then leaf BDD/mock/OS call sites. Do not run
semantic tests, post-RSS, parser scaling, or bootstrap until compiler check is
green.

Fixed post-migration RSS ceilings:

- Parser: 220,321 KiB.
- 10,000 distinct short texts: 494,199 KiB.
