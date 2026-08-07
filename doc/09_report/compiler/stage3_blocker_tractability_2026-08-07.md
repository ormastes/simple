# Stage-3 self-host blocker tractability assessment (2026-08-07)

## Scope and method

This is a **static, read-only assessment**. No build, cargo invocation,
bootstrap, or redeploy was run — per task constraint and the repo's current
94%-full-disk / prior-ENOSPC-tree-wipe history. All findings below are
derived from reading `doc/08_tracking/bug/*.md`, `git log`, and `git show`
against the current working tree (HEAD `05858d83c8b`, 1 commit ahead of
`origin/main` at `e258539bdc5` at assessment time) and are cited by
file:line and commit SHA. No decisive full Stage-3 run was performed by this
assessment; see "What remains unverified" for the exact experiment that
would close the loop.

## Verdict: PURE-SIMPLE — and, as far as static evidence shows, the entire
traced blocker chain is already source-fixed and landed

Tracing the actual Stage-3 failure chain (not the historical candidate list
in the task prompt) through `doc/08_tracking/bug/` turns up **seven
sequential blockers**, each discovered only after the previous one was
fixed and Stage 3 advanced further. **Every one of them originates in
`src/compiler/**` or `src/lib/**` (pure Simple) — none in
`src/compiler_rust/**`.** Every fix commit below is confirmed present on
both current `HEAD` and `origin/main` via `git merge-base --is-ancestor`.

| # | Failure | File:line (pure-Simple) | Fix commit | Landed? |
|---|---|---|---|---|
| 1 | `unresolved type: ByteOrder` (lazy import registration skips the `registering_import_symbols` guard) | `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:924` (`try_register_bootstrap_global_symbol`) | (BGS1, folded into resolver) | yes, per bug doc's RESOLVED section |
| 2 | `Effect` facade collision (`compiler.hir.hir_types::Effect::struct` vs `compiler.mir.mir_effects::Effect::enum`) | `src/compiler/50.mir/__init__.spl` re-export list | cycle-6 fix (facade re-export trim) | yes |
| 3 | Compiler's own `CodegenError` construction called unresolved `Array.first()`, SIGSEGV on every fatal MIR-lowering error | `src/compiler/80.driver/driver_aot_pipeline.spl` + 2 sibling files | length-guard rewrite, landed | yes |
| 4 | `Array.first()`/`.last()` MIR lowering: success path returned bare `LocalId` instead of `Some(LocalId)`, so it never engaged | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3645` | one-line `Some(result_local)` wrap | **yes — confirmed present in current tree** (`grep` hit) |
| 5 | Borrow-checker field-index collision: `resolve_field_index`'s id-keyed tier collides across module boundaries in an `--entry-closure` whole-program build, corrupting `NLLChecker.errors` reads (SIGSEGV `si_addr=0x118`) | `src/compiler/50.mir/_MirLowering/function_lowering.spl:934` | `b9e23914a0e` "resolve_field_index consults module-qualified struct_field_order tier before collided id-keyed field_map" | **yes — confirmed ancestor of HEAD and origin/main** |
| 6 | `SymbolTable.lookup`/`lookup_or_invalid` trap (`ud2`) on an out-of-range `scope_id` reaching `self.scopes[scope_id.id]` | `src/compiler/20.hir/hir_types.spl:410,439` | `976c44a28f6` "SymbolTable.lookup uses Dict-free scope-id range check, not rt_dict_contains" | **yes — confirmed present in current tree**, ancestor of HEAD |
| 7 | `asm """..."""` bare-template placeholders (`{addr}` etc.) with no operand list emitted literal `{`/`}` into LLVM inline asm, crashing the assembler 3 files were on the Stage-3 `--source` path (`compiler/35.semantics/volatile.spl`, `lib/.../semihost_transport.spl`, `lib/.../system_api.spl`) | see files above | `f7cf6c87b02` "close the asm-template placeholder family blocking Stage-3" + follow-up `39a2c7c2040` | **yes — confirmed ancestor of HEAD** |

Each row's discovery narrative in its own bug doc makes clear these were
found **serially**: a lane fixes blocker N, replays Stage 3 (via the cheap
"pinned stage2 + replay the recorded stage3 command" technique, not a full
`--full-bootstrap`), and Stage 3 advances further before hitting blocker
N+1. Blocker 7 (asm) is the most recent (2026-08-07), and its doc records
that the two remaining unconverted files (`src/os/kernel/arch/x86_64/{timer,topology}.spl`)
are **not** on the Stage-3 build graph at all (`src/os` is not one of the
`--source src/compiler --source src/lib --source src/app` roots the
bootstrap harness passes), so they do not block Stage 3.

Two remaining Stage-3 diagnostic-quality issues are open but are **not**
recorded as hard failures — they degrade the compiler's warning fidelity,
not its ability to complete:
- `doc/08_tracking/bug/stage3_unresolved_call_warning_family_2026-08-07.md`
  — Status: OPEN, "one member fixed"; the remaining members are an
  incomplete-warning-enumeration issue plus a cross-module static-method
  resolution hole, not a build-terminating error.
- `doc/08_tracking/bug/failed_to_load_imported_types_is_only_a_warning_2026-08-07.md`
  — Status: OPEN ("argued, not changed"); a fail-open severity classification
  issue (should be an error), not itself a crash.

## What remains unverified — the decisive experiment

No bug doc records a **single clean run of the full chain together**. Every
fix above was verified against a replay harness pinned at the commit that
introduced *that* fix, then the next lane started from a *different*
pinned/rebuilt worktree to chase the *next* blocker. There is no artifact on
record showing blockers 1–7 all fixed simultaneously in one tree producing a
complete `stage3-simple` binary. This is a real gap, not a formality:
`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
explicitly warns that fixing one member of a resolver-defect family and
declaring victory is exactly how blocker 1 → blocker "next" repeated twice
already (`cache_validator.spl` fixed, `watcher_client.spl` next in line).

**The decisive experiment** (not run here, per task constraint): replay
Stage 3 alone (not `--full-bootstrap`) against the current HEAD using the
same cheap technique multiple lanes already used —
`build/cyc/build_stage2.sh` + `build/cyc/run_stage3.sh` against a pinned
stage2, per
`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`'s
"RED → GREEN method" section (stage2 rebuild ~2m50s, Stage 3 to the prior
HIR wall ~2m; the full MIR-lowering pass that blocker 5/6 sit in ran ~394s
in the last recorded replay). This does not require `--full-bootstrap`
(no Rust seed rebuild), so it does not carry the ENOSPC/tree-wipe risk that
motivated banning builds in this assessment — but it is still a real build
and was explicitly out of scope here.

## Why this matters for the campaign's last 9 units

If the decisive experiment above confirms Stage 3 now completes, the
campaign's last 9 units are unblocked **without any Rust-seed change** — an
operator only needs to run the (cheap, seed-reuse) Stage 3 replay or, if
that's clean, the full `bootstrap-from-scratch.sh --deploy` (non-full,
seed-reusing path) to get a genuine self-hosted `bin/simple`. Nothing in the
traced chain requires `--full-bootstrap` (i.e., no `src/compiler_rust`
change was needed for any of the 7 fixes) — so a fresh Rust seed rebuild is
not implicated at all; the existing seed can still build stage2 the same way
it always has, since the Rust seed rebuild is only needed for
`src/compiler_rust` changes, and every fix above lives in `src/compiler`/
`src/lib`, which the seed already knows how to compile per the standard
"reuse the existing seed" incremental-bootstrap path documented in
`.claude/rules/bootstrap.md`.

## Sources

- `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
- `doc/08_tracking/bug/mir_lowering_codegen_error_first_call_zero_core_dump_2026-08-06.md`
- `doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`
- `doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md`
- `doc/08_tracking/bug/asm_template_placeholders_never_bind_2026-08-07.md`
- `doc/08_tracking/bug/run_subcommand_absent_from_staged_bootstrap_binaries_2026-08-07.md`
- `doc/08_tracking/bug/stage3_unresolved_call_warning_family_2026-08-07.md`
- `doc/08_tracking/bug/failed_to_load_imported_types_is_only_a_warning_2026-08-07.md`
- `.claude/rules/bootstrap.md`
- Commits: `b9e23914a0e`, `976c44a28f6`, `f7cf6c87b02`, `39a2c7c2040`,
  `030ff43e330`, `9bb8727cbc3` (superseded), `548f2d3b1f6`
