# Full-CLI self-hosted `bin/simple` native build: two concrete backend blockers

- Date: 2026-08-27
- Blocks: deploying a self-hosted full CLI, which is the documented unblock for
  ~311 ORA-001/ORA-002-blocked specs (see
  `source_grep_guard_specs_blocked_on_selfhosted_binary_2026-08-26.md`).

## Setup that got this far

Bootstrap is 3-stage green with a self-hosted fixpoint (stage2 hash == stage3
hash `ce895e970d70`, log `/tmp/boot8.log`; repairs landed via PR #91). Building
the full CLI with the fresh `bootstrap/stage3/simple`:

```bash
SIMPLE_RUNTIME_PATH=$PWD/src/compiler_rust/target/release \
  bootstrap/stage3/simple native-build --source src/app --entry-closure \
  --strip --threads 8 --entry src/app/cli/main.spl -o bootstrap/full_cli/simple
```

gets far past where the seed dies and fails with TWO distinct errors.

## Blocker A (seed interpreter, whole-program registry corruption)

Building with the SEED (`bin/release/x86_64-unknown-linux-gnu/simple`) instead
dies earlier with:

```
error: semantic: method `len` not found on type `i64` (receiver value: 265)
```

No file:line; single-threaded rerun does not localize it. This is the KNOWN
OPEN seed defect class of
`mcp_stdio_smoke_seed_flat_registry_len_i64_2026-07-17.md`: an unrelated call
corrupts to i64 when a large import closure (~1872 modules here) is present.
Workaround = don't use the seed; use stage3 (above).

## Blocker B1: RESOLVED (2026-08-27) — lexer, not MIR

Root cause refined: the trigger is a variable NAMED `skip`. `skip` lexes as
`TokenKind::Skip` unless followed by `(` (lexer/identifiers.rs); the
statement dispatcher then consumed the bare `skip` and left `["a"] = 1` to
parse as the NEXT statement — an assignment with an array-literal target —
which MIR rightly rejected as `complex lvalue: Array`. The two `self.tests[i]`
sites named below were innocent (array stores through field receivers compile
fine); the failing function, `prune_timing_runs` (test_db_core.spl:~471),
declares `var skip: Dict<i64,i64>` and does `skip[tid] = ...`.

Fix: lexer contextual case extended to `skip[` (`self.check('[')`) — a skip
statement is never followed by `[`, so `skip[` is always an index expression.
`src/compiler_rust/parser/src/lexer/identifiers.rs`. Repro + neighbor spec
(old seed RED 2/3, fixed seed GREEN 3/3):
`test/01_unit/compiler/parser_skip_contextual_keyword_dict_index_spec.spl`.
Still broken (same class, NOT fixed): `skip` as a parameter/field name —
`fn f(skip: bool)` fails with `expected identifier, found Skip` (parse-keyword
path covers primary expressions, not declaration names). No in-tree call site
found; fix when one appears.

Historical text (kept for context):

```
src/lib/nogc_sync_mut/test_runner/test_db_core.spl:
mir: Unsupported HIR construct: complex lvalue: Array([HirExpr { kind: Local(3), ty: TypeId(5) }])
```

Triggered by array-element stores through a field receiver, e.g.
`self.tests[test_idx] = t` (test_db_core.spl:302) and `self.counters[i] = c`
(:347). The Rust `lower_lvalue`
(`src/compiler_rust/compiler/src/mir/lower/lowering_gpu.rs:480-514`) has
`Local`/`FieldAccess`/`Index` arms but the HIR produced here presents an
`Array`-kind lvalue that falls into the catch-all `complex lvalue: {:?}` arm
(:596). Same family as the `complex lvalue: Deref` rejection worked around
field-wise in `src/os/kernel/arch/riscv64/interrupt.spl:388`. Fix belongs in
the MIR lowerer (add the Array-lvalue arm or fix the HIR shape), NOT in
test_db_core.spl — array element assignment is core language semantics.

## Blocker B2: 17 file_system function bodies fail codegen

```
src/lib/nogc_sync_mut/file_system/utilities.spl:
codegen: 16 function body/bodies failed to compile:
[temp_file_create, temp_file_create_with_name, temp_dir_create,
temp_file_cleanup, glob_find, tree_create, tree_print_recursive,
symlink_resolve, disk_usage, file_mime_type, file_is_text,
files_filter_by_extension, files_group_by_extension, file_line_count,
file_word_count, file_char_count]
src/lib/nogc_sync_mut/file_system/watch.spl: codegen: 1 body [watch_create]
```

No per-function reason is printed. `SIMPLE_ALLOW_STUB_FALLBACK` exists but is
explicitly unsafe (silent misbehavior) — not a fix.

## Next steps

1. ~~Fix B1~~ DONE (see above; parser fix + spec, needs seed rebuild + PR).
2. Re-run to get per-function reasons for B2 (likely extern/SFFI shape gaps).
3. Rebuild stage3, retry full-CLI build, deploy to
   `bin/release/x86_64-unknown-linux-gnu/simple` (+ `linux-x86_64` launch
   path), verify `--version` shows no seed banner.
