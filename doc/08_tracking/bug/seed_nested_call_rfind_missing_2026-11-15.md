# str.rfind / last_index_of not found in nested call context (seed interpreter)

- id: seed_nested_call_rfind_missing_2026-11-15
- status: open (seed side); Simple call site worked around
- component: seed interpreter (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`, `call_method_on_value`, `Value::Str` arm)
- found by: `simple lint` on any `src/compiler/**` file dying with
  `error: semantic: src/app/cli/lint_entry.spl:481:9: method 'rfind' not found on value of type str in nested call context`
- sibling of: `str_byte_len_not_found_in_nested_call_context_2026-11-12`, `interp_str_substring_nested_call_dispatch_2026-08-19`

## Symptom
A str method called on a method-call result (`x.replace(a, b).rfind(c)`) fails under
the seed interpreter (`test`, `lint`) with METHOD_NOT_FOUND "in nested call context".
`run` of the same code goes through the JIT path and prints the right value, which is
why a plain `run` repro looks clean. Hoisting the receiver into a `val` works.

The error's FILE is misattributed: it names the entry module (`lint_entry.spl`, or the
spec file under `test`) with the LINE:COL of the real site, here
`src/compiler/90.tools/fix/rules/impl_/lint_star_import.spl:481:9`.

## Root cause
Chained receivers are evaluated into a `Value` and dispatched through
`call_method_on_value`, whose `Value::Str` arm carries its own subset of str methods
(`len`, `byte_len`, `find`/`index_of`, `slice`, `replace`, `split`, ...). `rfind` /
`last_index_of` exist in the direct-receiver arm (`interpreter_method/string.rs:402`)
but not in the chained arm. Present in the seed source at release tip `fa2dd425635`,
so this is a seed limitation, not a stale-seed mismatch.

## Minimal repro (fails under `<seed> test`)
```simple
use std.spec.*

fn last_slash(entry: text) -> i64:
    val slash = entry.replace("\\", "/").rfind("/")
    slash

describe "nested rfind":
    it "works on a chained receiver":
        expect(last_slash("a/b")).to_equal(1)
```

## Workaround applied
`lint_star_import.spl` `_resolve_numbered` binds the normalized path to a `val`
before calling `rfind` (introduced by `70f8df9766d`, 2026-11-14). Regression spec:
`test/01_unit/compiler/lint/star_import_fix_edit_spec.spl`
("narrows a compiler star import through a numbered layer dir").

## Seed fix (not done here — Rust untouched by this lane)
Add `"rfind" | "last_index_of"` to the chained `Value::Str` arm, matching
`interpreter_method/string.rs`, with a unit test next to
`nested_substring_dispatches_byte_indexed_on_temporary_text`.

## 2026-11-26 — Rust Seed Root Fix (WA-P6, `ROOT-FIXED+SEED-GATED`)
- Fixed chained `Value::Str` method dispatch in
  `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
  (`call_method_on_value`) to handle `"last_index_of" | "rfind"`, delegating
  to `eval_string_method` matching `interpreter_method/string.rs`.
- Added unit test `nested_rfind_and_last_index_of_dispatch_on_temporary_text` in
  `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`.
- Kept caller guard in `src/compiler/90.tools/fix/rules/impl_/lint_star_import.spl:481`
  with `@workaround bug=seed_nested_call_rfind_missing_2026-11-15 recover=8e96296d9e6 reason=ROOT-FIXED+SEED-GATED: ...`
  so pre-fix bootstrap seeds continue passing until Stage 2 rebuilds.
- Verified:
  - `cargo test -p simple-compiler --lib -j 4 interpreter_helpers::method_dispatch`: `11 passed; 0 failed`
  - `test/01_unit/compiler/wa_src_lane3_workarounds_spec.spl --mode=interpreter`: `7 passed, 0 failed`
  - `test/01_unit/compiler/lint/star_import_fix_edit_spec.spl --mode=interpreter`: `8 passed, 0 failed`



## Shard Registration (2026-11-27)

- **Workaround site:** `src/compiler/90.tools/fix/rules/impl_/lint_star_import.spl:481-483` (`_resolve_numbered`, tagged `# @workaround bug=seed_nested_call_rfind_missing_2026-11-15 recover=8e96296d9e6 reason=ROOT-FIXED+SEED-GATED`).
- **Verification (`wa3_shared_bin/simple.exe --mode=interpreter`):** `test/01_unit/compiler/lint/star_import_fix_edit_spec.spl` 8/8 PASS, `test/01_unit/compiler/wa_src_lane3_workarounds_spec.spl` 7/7 PASS.
- **Shard:** `doc/08_tracking/bug/db/seed_nested_call_rfind_missing_2026-11-15.sdn` (`status=fix-implemented-verification-pending`, waiting for pre-fix frozen Stage-1 seed binaries to be superseded before retiring the workaround).
