# Simple Language Compiler

**Self-hosted compiler written in Simple.** Bootstrap: Rust seed → Simple compiler → self-hosted binary.
Impl in Simple unless it has big performance differences.

## Essential Commands
```bash
bin/simple build                  # Debug build (lint/fmt/check/bootstrap subcommands also available)
bin/simple test                   # Run all tests (or: test path/to/spec.spl)
scripts/bootstrap/bootstrap-from-scratch.sh --deploy  # Full bootstrap
```

## FreeBSD QEMU Bootstrap Check
From Linux, do not stop at `bootstrap-freebsd-seed.sh` saying it must run on
FreeBSD. Use the repo-managed automated wrapper:

```bash
sh scripts/check-freebsd-bootstrap-qemu.shs --smoke
```

Use `--full` for the repeated bootstrap verification pass. The wrapper creates
`build/freebsd/vm/freebsd-cloudinit-seed.iso` from the host SSH public key,
downloads a pristine FreeBSD `BASIC-CLOUDINIT-ufs` base qcow2, creates a fresh
working overlay for the run, starts QEMU with SSH forwarding on port `2222`, and
logs in as the default `freebsd` cloud user. Env knobs: `QEMU_VM_PATH`,
`QEMU_BASE_VM_PATH`, `QEMU_CLOUDINIT_ISO`, `QEMU_SSH_PUBLIC_KEY`, `QEMU_PORT`,
`QEMU_USER`, `QEMU_MEM`, `QEMU_CPUS`. For manual VM debugging:

```bash
bin/simple run src/app/test/freebsd_qemu_setup.spl --download --quick
```

## Critical Rules
- **jj** for VCS — `jj commit -m "msg"` / push: `jj bookmark set main -r @- && jj git push --bookmark main`
- **NEVER create branches** — work directly on `main`
- **ALL code in `.spl`/`.shs`** — no Python/Bash (except 3 bootstrap scripts)
- **NO inheritance** — use composition, traits, mixins. **Generics:** `<>` not `[]`
- **NEVER skip** failing tests without approval. **NEVER convert TODO to NOTE** — implement or delete
- When a short, safe grammar or compact expression form fails, compiles too slowly, or forces a workaround, fix it or record a concrete bug/feature request instead of silently normalizing the workaround
- When you hit a meaningful perf regression during implementation or verification, either fix it in the same change or record it as a concrete bug/todo before moving on
- **NEVER over-engineer.** **DO NOT ADD REPORT TO GIT** unless requested
- **MDSOC+ by default** — use MDSOC outer + ECS business layer for userland services/apps; kernel/drivers stay MDSOC-only. See `doc/04_architecture/mdsoc_architecture_tobe.md` (MDSOC+ section)

## Owned-Code Scope
- For code counts, reviews, verification scans, and summaries, ignore vendored or third-party runtime source unless the user explicitly asks to inspect it.
- External paths: `src/compiler_rust/vendor/**`, `src/runtime/vendor/**`, `src/runtime/miniaudio.h`, `src/runtime/stb_image.h`, `src/runtime/stb_truetype.h`.

## Detailed Rules & Reference
- **Rules:** `.claude/rules/` — `language.md`, `testing.md`, `bootstrap.md`, `commands.md`, `structure.md`, `code-style.md`, `vcs.md`
- **Skills:** `.claude/skills/` — invoke `/skill-name` (`/sstack`, `/dev`, `/coding`, `/test`, `/debug`, etc.)
- **Agents:** `.claude/agents/` — `code`, `test`, `debug`, `explore`, `docs`, `vcs`, `infra`, `build`, `ml`
- **Memory refs:** `.claude/memory/ref_*.md` — architecture, coding, SFFI, stdlib, CUDA, etc.
- **Syntax:** `doc/07_guide/quick_reference/syntax_quick_reference.md`
