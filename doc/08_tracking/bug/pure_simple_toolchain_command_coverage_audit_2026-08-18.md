# Pure-Simple self-hosted toolchain: command-coverage audit + `native-build --help` segfault

Date: 2026-08-18
Status: audit RECORDED; one gap FIXED in source (needs a bootstrap redeploy to land in the capsule)

## 0. Difficulty estimate (stated up front)

**Hard.** Not conceptually — the ground-truth part is a handful of `--version`
probes — but because every honest measurement here is expensive (`bin/simple
test` carries a ~310 s fixed session setup; `lint` is superlinear; a full
bootstrap is out of budget), the worktree is shared with sessions that replace
`bin/simple` mid-run, and `origin/main` is currently unbuildable from other
sessions' half-landed Rust changes. The audit therefore had to be built from
cheap, repeatable binary probes rather than from a rebuild.

## 1. Ground truth: what is deployed

Method: `readlink -f` + `stat` + `sha256sum` + each binary's own version banner.
Recorded at the moment of measurement because other sessions replace these files.

| path | sha256 (prefix) | size | mtime |
|---|---|---|---|
| `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple` | `4129e2a7d62e…` | 59,546,088 | 2026-08-18 07:53:39 |
| `bootstrap/stage2/simple` | `905ce03696a4…` | 3,464,072 | 2026-08-11 22:10:05 |
| `bootstrap/stage3/simple` | `905ce03696a4…` | 3,464,072 | 2026-08-11 22:10:05 |
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | `905ce03696a4…` | 3,464,072 | 2026-08-11 22:10:05 |

Two facts follow directly:

- **`bin/simple` IS the Rust seed, and says so.** Verbatim, first two lines of
  `bin/simple --version`:

  ```
  WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
  Build and use the pure-Simple bin/simple instead.
  Simple Language v1.0.0-RC
  ```

  This confirms `.claude/rules/commands.md`. It also means CLAUDE.md's rule
  ("default tooling = pure-Simple self-hosted binary … `test`/`lint`/`fmt`/
  `build`/`run`/MCP/LSP all run on `bin/release/<triple>/simple`") is satisfied
  only *pathwise*: that path currently holds the seed, so every one of those
  lanes is in fact running the seed.
- **stage2 and stage3 are byte-identical** (same sha256). The bootstrap
  fixpoint held for that build. Note the mtime: the pure-Simple capsule on disk
  is from 2026-08-11, a week older than the seed.

FALSIFIED BY: re-running the four commands above and getting a different
sha256/banner — expected, and the reason identity is recorded inline rather
than asserted as a standing fact.

## 2. Audit: which commands exist on the pure-Simple binary

Method: invoke each subcommand on `bootstrap/stage3/simple` and read the exit
status **directly** (`cmd >/dev/null 2>&1; echo $?`), never through a pipe — a
first pass through `| head` reported `exit=0` for everything, which is `head`'s
status, not the compiler's. That mistake is recorded here deliberately: it is
the same shape as the miscounts that have been quoted and retracted this week.

Verbatim results, `bootstrap/stage3/simple <cmd> --help`:

```
run            error: unknown command 'run'              exit 1
test           error: unknown command 'test'             exit 1
build          error: unknown command 'build'            exit 1
lint           error: unknown command 'lint'             exit 1
fmt            error: unknown command 'fmt'              exit 1
doc-coverage   error: unknown command 'doc-coverage'     exit 1
todo-scan      error: unknown command 'todo-scan'        exit 1
stats          error: unknown command 'stats'            exit 1
info           error: unknown command 'info'             exit 1
desugar        error: unknown command 'desugar'          exit 1
check          error: unknown command 'check'            exit 1
compile        error: missing source file                exit 1   (command EXISTS)
native-build   Segmentation fault                        exit 139 (command EXISTS)
```

And `bootstrap/stage3/simple --help` states the surface explicitly:

```
Simple Bootstrap Compiler v1.0.0-beta
Built from Simple source via the staged bootstrap

Commands:
  compile <file> --format=smf   Compile to SMF (the ONLY format `compile` supports)
  native-build <file>.spl       Compile to a native executable
```

**The central finding.** The pure-Simple binary produced by the bootstrap is not
a partially-complete replacement for the seed — it is a *different program with
a two-command surface*: `compile` and `native-build`. It is `src/app/cli/
bootstrap_main.spl`, not `src/app/cli/main.spl`. The distance from "replace the
seed" is therefore not "N commands are buggy"; it is "11 of the 13 audited
commands are not wired into the shipped capsule's entry point at all". This is
consistent with, and sharpens, the existing note in `.claude/rules/commands.md`
("No pure-Simple binary can lint: `bootstrap/stage3/simple lint` is
`unknown command`").

MCP/LSP servers were **not** probed as pure-Simple: `bin/release/*/simple_mcp_server`
and `simple_lsp_mcp_server` are separate binaries with their own build lineage;
claiming anything about them from this audit would be unsupported. Stated as a
gap, not a result.

FALSIFIED BY: `bootstrap/stage3/simple run --help` printing usage instead of
`unknown command`; or the bootstrap producing a capsule whose entry point is
`src/app/cli/main.spl`.

## 3. The gap chosen, and why

Candidates considered:

| candidate | why not |
|---|---|
| Wire `run`/`test` into the capsule | Requires the full CLI dispatch + driver closure in the bootstrap entry. Not small; it is the whole self-hosting program. |
| `lint` on pure Simple | Blocked upstream by the lint cost defect (`lint_timeout_hwir_zca_rows_2026-08-17.md`). |
| `--list-optimizations` in pure Simple | Needs the seed's optimization registry ported. Real work, low leverage. |
| **`native-build --help` segfault** | **Chosen.** A *shipped* command of the pure-Simple binary crashes on its most basic invocation. Small, self-contained, and it removes a hard crash rather than adding a feature. |

Choosing a segfault-removal over a feature-add is deliberate: a crash in one of
the only two commands the capsule actually has is a worse signal about
self-hosting readiness than any missing command, and it is the one thing in this
list that can be closed honestly in a single edit.

## 4. Defect: `native-build --help` segfaults on the pure-Simple capsule

Reproduce (verbatim, exit codes read directly):

```
$ bootstrap/stage3/simple native-build --help   -> Segmentation fault, exit 139
$ bootstrap/stage3/simple native-build -h       -> Segmentation fault, exit 139
$ bootstrap/stage3/simple native-build          -> Segmentation fault, exit 139
$ bootstrap/stage3/simple native-build nonexist.spl
[ERROR] phase 2 FAILED
error: in-process native-build: native entry source not found: nonexist.spl   exit 1
$ bootstrap/stage3/simple compile --help
error: missing source file                                                    exit 1
```

Note the contrast: the *same binary* handles the missing-source case gracefully
for `compile`, and handles a bad positional gracefully for `native-build`. Only
the shapes with **no usable positional** crash.

Root cause. In `src/app/cli/bootstrap_main.spl`, `run_native_build_bootstrap`
routed `--help` / `-h` / `--list-optimizations` — and, by falling through
`native_build_single_spl_positional() == ""`, the no-argument case — into
`run_rt_native_build`, whose body is the Rust seed extern declared at line 2:

```
extern fn rt_native_build(args: [text]) -> i64
```

In the pure-Simple capsule that extern is only a **backfilled stub** (see the
seed-owned-extern backfill in `src/compiler/70.backend/backend/llvm_native_link.spl`
:1161-1176, which exists precisely so the link does not die with
`undefined symbol: rt_native_build`). Calling it jumps into nothing. The seed
binary never shows this because there the extern is real.

Secondary finding, recorded because it is a trap for the obvious fix:
`native_build_help()` (`bootstrap_main.spl:18`) looks like the place to put the
text, and is even listed in `bootstrap_function_names()`
(`src/compiler/80.driver/driver_bootstrap.spl:88`). It is **not** usable: its
body is hardcoded in bootstrap MIR lowering
(`src/compiler/50.mir/_MirLowering/module_lowering.spl:566-576`) to emit
`return 0`, so any edit to its `.spl` source is silently ignored in the capsule.

FALSIFIED BY: `native-build --help` on a freshly bootstrapped capsule printing
usage before this fix; or `rt_native_build` resolving to a real implementation
inside the stage3 capsule.

## 5. Fix

`src/app/cli/bootstrap_main.spl`, in `run_native_build_bootstrap`:

- `--help` / `-h` now print usage in-process and `return 0`. No FFI.
- Bare `native-build` (`args.len() < 3`) now prints `error: missing source file`
  plus usage and returns 1, matching `compile`'s behaviour.
- `--list-optimizations` is **knowingly left** on the seed FFI route: it is a
  data query against the seed's optimization registry, and faking it would be
  worse than the crash. It remains a known pure-Simple crash and is scoped out
  of this change on purpose.

## 6. Verification, and its honest limits

Regression cover:
`test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl`

```
SPEC FILE VERDICT: ... outcome=OK declared>=4 executed=4 passed=4 failed=0
PASS test/01_unit/app/cli/bootstrap_native_build_help_no_seed_ffi_spec.spl
```

Reproduce-first was proven mechanically rather than asserted, by grepping each
asserted string against `git show HEAD:src/app/cli/bootstrap_main.spl`:

```
HEAD=0 NOW=1  if removed_bundle == "--help" or removed_bundle == "-h":
HEAD=0 NOW=1  if args.len() < 3:
HEAD=1 NOW=0  if removed_bundle == "--help" or removed_bundle == "-h" or removed_bundle == "--list-optimizations":
```

All three invert, so 3 of the 4 examples would have failed at HEAD.

**Limit, stated plainly: the fix is not yet proven on a binary.** It is a source
change, and `bootstrap/stage3/simple` is a prebuilt capsule from 2026-08-11.
Confirming that `native-build --help` no longer segfaults requires a full
bootstrap redeploy, which was out of budget and out of scope for this session
(deploying over `bin/simple` was explicitly prohibited). Until that redeploy,
the deployed capsule still crashes. The spec is deliberately a SOURCE contract
for this reason, and says so in its header.

Pre-existing red, not caused by this change:
`test/01_unit/app/cli/bootstrap_main_source_spec.spl` reports 6 passed / 10
failed. The failures name `__init__.spl` vs `mod.spl`, the lexer, the I/O
runtime and the browser render backend — files this change never touches — and
every `bootstrap_main.spl` string those examples assert still greps present
(`val first = all_args[1]`, `if first == "native-build"`,
`return run_native_build_bootstrap(all_args)`,
`pub fn run_native_build_bootstrap(args: [text]) -> i64:`,
`return run_exact_stage4_focused_capsule(args)`, and `if argc > 2` correctly
absent). FALSIFIED BY: reverting this change and finding that spec green.

Also noted and worked around, not caused here: `origin/main` currently does not
build the Rust seed (duplicate `INLINE_INT_BITS`/`fits_inline_int` in
`runtime/src/value/core.rs`, E0432 `module_globals_generation`, E0599
`f.as_ref()`), from other sessions' half-landed changes. No rebuild of the seed
was attempted; the already-deployed seed binary was used as-is.

## 7. Open follow-ups

- `native-build --list-optimizations` still segfaults on the pure-Simple
  capsule (same seed-extern root cause, deliberately unfixed).
- The capsule's entry point is `src/app/cli/bootstrap_main.spl`, not
  `src/app/cli/main.spl` — 11 of 13 audited commands are absent by
  construction. That, not per-command bugs, is the actual distance to replacing
  the seed.
- MCP/LSP server binaries were not audited for pure-Simple provenance.
