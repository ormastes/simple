# SPipe — Index

> **SPipe** = **S**imple **Pipe** — the spec → test → report pipeline.
> Renamed from `sspec` on 2026-04-26.

## Skill harness

| File | Purpose |
|------|---------|
| [`skill.md`](skill.md) | Test-writing skill: BDD syntax, matchers, file structure, doc generation |
| [`loop.md`](loop.md) | Continuous check-and-implement loop (`/spipe_loop`) |
| [`guide.md`](guide.md) | Pointer to the canonical testing guide at `doc/07_guide/testing/testing.md` |
| [`lint_rules.md`](lint_rules.md) | Lint-rules design doc (relocated from `doc/05_design/`) |

## Skill entry-point

The Claude Code skill lives at `.claude/skills/spipe.md` and dispatches into
this directory. Slash invocation: `/spipe`.

## Template

Test scaffolding template: `.claude/templates/spipe_template.spl`.

## Source code

The runtime/compiler side of SPipe lives at:

- `src/lib/nogc_sync_mut/spipe.spl` — runtime spec library
- `src/compiler_rust/lib/std/src/spec/spipe_docgen.spl` — doc generator
- `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/spipe_collector.spl` — dashboard collector
- `src/compiler_rust/compiler/src/lint/checker_spipe.rs` — lint checker
- `src/compiler_rust/driver/src/cli/migrate/spipe.rs` — migrate CLI
- `src/compiler_rust/driver/src/cli/spipe_docgen/` — driver-side docgen module
- `src/app/spipe_docgen/` — app-side docgen
- File extension `.spipe` (e.g. `src/compiler/60.mir_opt/optimization_passes.spipe`)

## Historical record

Past development reports are kept under `doc/09_report/.../sspec_*.md` with
their original filenames as a dated incident record. They describe the
old name; do not retroactively rename.

## Migration manifest (2026-04-26)

| Old path | New path |
|----------|----------|
| `.claude/skills/sspec_loop.md` | `doc/00_llm_process/spipe/loop.md` (+ thin `.claude/skills/spipe.md` and `.claude/skills/spipe_loop.md`) |
| `.claude/skills/lib/sspec.md` | `doc/00_llm_process/spipe/skill.md` |
| `doc/05_design/sspec_lint_rules_design.md` | `doc/00_llm_process/spipe/lint_rules.md` |
| `doc/06_spec/app/compiler/sspec_guide.md` | `doc/00_llm_process/spipe/guide.md` (thin redirect to `doc/07_guide/testing/testing.md`) |
| `tools/claude-plugin/sstack-lang/skills/sspec_loop.md` | `tools/claude-plugin/sstack-lang/skills/spipe_loop.md` |
| `doc/00_llm_process/skill_command/skills/claude/lib/sspec/` (dir) | `.../lib/spipe/` (dir) |
| `src/lib/nogc_sync_mut/sspec.spl/.smf` | `src/lib/nogc_sync_mut/spipe.spl/.smf` |
| `src/compiler_rust/compiler/src/lint/checker_sspec.rs` | `checker_spipe.rs` |
| `src/compiler_rust/driver/src/cli/migrate/sspec.rs` | `migrate/spipe.rs` |
| `src/compiler_rust/driver/src/cli/sspec_docgen/` (dir) | `cli/spipe_docgen/` |
| `src/compiler_rust/lib/std/src/spec/sspec_docgen.spl` | `spipe_docgen.spl` |
| `src/compiler_rust/lib/std/src/tooling/dashboard/collectors/sspec_collector.spl` | `spipe_collector.spl` |
| `src/app/sspec_docgen/` (dir) | `src/app/spipe_docgen/` |
| `src/compiler/60.mir_opt/optimization_passes.sspec` | `.spipe` (file extension) |
| `.claude/templates/sspec_template.spl` | `.claude/templates/spipe_template.spl` |
| `test/integration/app/sspec_quality_lint_spec.spl` | `spipe_quality_lint_spec.spl` |
| `test/unit/compiler/backend/sspec_system_test_spec.spl` | `spipe_system_test_spec.spl` |
| `doc/10_metrics/dashboard/tables/sspec_tests.sdn` | `spipe_tests.sdn` |
| `examples/.../hello_riscv32_sspec.{elf,s}` | `hello_riscv32_spipe.{elf,s}` |
| `examples/.../riscv32_test/sspec_baremetal.h` | `spipe_baremetal.h` |

In-file string sweep (case-preserving `sspec→spipe`/`SSpec→SPipe`/`SSPEC→SPIPE`):
- 529 code files (`.rs`/`.spl`/`.smf`)
- 28 config/script files (`.toml`/`.json`/`.shs`/`.sh`/`.cmd`/`.sdn`)
- 5 assembly/header files (`.s`/`.h`/`.c`/`.cpp`)
- 169 narrative `.md` files

### Out of scope (kept as-is)
- `doc/09_report/...sspec_*.md` — historical incident reports
- `.claude/worktrees/**` — parallel-agent worktrees re-snapshot from main
- `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, vendored third-party
