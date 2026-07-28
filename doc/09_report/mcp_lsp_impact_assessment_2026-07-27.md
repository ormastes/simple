# MCP/LSP impact assessment — 2026-07-27 compiler landing

**Scope:** read-only investigation. No build, bootstrap, or redeploy was run.
One trivial invocation was executed for evidence: `bin/simple --version`
(prints a version banner; not a build).

## Bottom line

The live MCP/LSP servers are **not exposed** to today's ~12 compiler-source
changes right now, for two independent reasons that both have to hold for a
future redeploy to also be safe:

1. The frozen native server binaries predate every relevant commit (bound #2).
2. The subprocess target those servers shell out to for actual language
   queries (`bin/simple`) is **currently the Rust seed**, not a rebuild of the
   self-hosted compiler — so even a live process restart today would not pick
   up the `.spl`-side HIR/driver/parser changes (see "Unexpected finding").

---

## 1. Dependency-closure finding

Both server entry points are **thin JSON-RPC wrappers that subprocess out to
`bin/simple`**, not binaries that statically link the compiler driver/HIR
pipeline:

- `src/app/simple_lsp_mcp/tools.spl:17-63` — `run_lsp_query()` /
  `run_diagnostics_query()` shell out via `process_run_bounded(find_simple_binary(), ...)`
  to `src/lib/nogc_sync_mut/lsp/lsp_query.spl` and `simple check`. Its own
  `use` graph (`main.spl:6-16`, `tools.spl:5-11`, `json_helpers.spl:9`,
  `protocol.spl:5`, `startup_log.spl:4-5`) touches only `std.io_runtime`,
  `std.log`, `std.file_system`, `std.nogc_sync_mut.io.process_ops`, and local
  `.` siblings — **zero** imports of `20.hir`, `80.driver`, or `10.frontend`.
- `src/app/mcp/main.spl` and its `.` siblings likewise contain no `use` of
  compiler-driver modules; `src/app/mcp/cli_passthrough.spl:3-21` and
  `main_lazy_query_tools.spl:66-` (`_mcp_find_simple_binary`) follow the same
  subprocess pattern. `api_tools.spl:81` and `main_lazy_query_tools.spl:36`
  match on "hir"/"10.frontend" only as **string literals** in tool
  descriptions/comments — confirmed by direct grep of the matched lines, not
  code references.

Confirmed via `grep -rln '20\.hir\|hir_lowering\|driver_source_loading\|80\.driver\|10\.frontend\|parser_decls_use' src/app/mcp src/app/simple_lsp_mcp` → only the two string-literal hits above, no `use` statements.

**Consequence:** today's changed files —
`src/compiler/20.hir/hir_lowering/**`, `src/compiler/80.driver/driver_source_loading.spl`,
`src/compiler/10.frontend/core/parser_decls_use.spl` — are **not in the
compile-time dependency closure of either server binary**. They only reach
the servers' *behavior* indirectly, through whatever binary
`find_simple_binary()` resolves to at query time (see §3/§5).

## 2. Live-binary staleness bound

```
bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server  6997688 bytes  2026-07-25 07:44:26
bin/release/x86_64-unknown-linux-gnu/simple_mcp_server      7513800 bytes  2026-07-25 07:44:26
```

Every commit cited in the concern is timestamped `2026-07-27 13:09` through
`22:44` (`git log`, author dates: `559832a135b` 13:09:01, `67024e9c0a5`
14:44:24, `8af2dc55596` 21:42:14, `3eea09c6796` 22:01:29, `e0f6d761320`
22:19:33, `584e74ece31` 22:44:56). **All postdate the Jul-25 07:44 native
binaries by ~1.5 days.** The wrappers at `bin/simple_lsp_mcp_server` /
`bin/simple_mcp_server` (`bin/simple_lsp_mcp_server:145-168`) `exec` exactly
that native artifact (`${script_dir}/release/${platform_dir}/simple_lsp_mcp_server`)
after a startup probe — there is no live-reload path. `ps aux` confirms every
running `simple_mcp_server` / `simple_lsp_mcp_server` process resolves to that
same `bin/release/x86_64-unknown-linux-gnu/` path.

**Blast radius bound: zero**, for the compiled server artifacts, until someone
redeploys.

## 3. Canonicalization risk to LSP resolution — mostly moot for MCP/LSP specifically, but real for a redeploy

`doc/09_report/review_canonicalization_2026-07-27.md` (dated `2026-07-27 23:09`,
i.e. written after these commits) already answers this directly, at **S7**:

> `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` is set at `driver.spl:590` only under
> `nb_entry_env != "" and ... self.ctx.options.mode == CompileMode.Aot`.
> Therefore `bin/simple test`, `bin/simple run`, `CompileMode.Check`, **LSP
> and MCP never take the new branch** and retain the sibling-resolution bug
> this commit exists to fix.

So the specific canonicalization commits (`584e74ece31`, `3eea09c6796`) gate
on `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` + `CompileMode.Aot` — a native-AOT
build mode LSP/MCP's `Check`/interpreter-mode queries never enter. **If the
servers were rebuilt today, go-to-definition/diagnostics would not flip
behavior from these two commits specifically** because that code path is
inert for them.

That does **not** clear the broader risk the task asked about, though:

- The review's S2/S3 findings (`review_canonicalization_2026-07-27.md:54-114`)
  show that for the **native-AOT entry-closure path** (used by
  `bootstrap-focused-native-build` style redeploys, not the interpreter-mode
  LSP), `src/app/lsp/server.spl` — a symlink to
  `src/lib/nogc_sync_mut/lsp/server.spl` — canonicalizes to
  `lib.nogc_sync_mut.lsp.server` as its *primary* spelling, with `app.lsp.server`
  demoted to alias #2, and the commit's own "Follow-up (not done here)" note
  admits `src/app/lsp` needs a reverse route table that doesn't exist yet
  (S2). Combined with S3, an `--entry src/app/lsp/...` **native build** risks
  `entry_main_symbol` mismatching and no `__simple_main` being emitted —
  i.e., a **build/link failure**, not a wrong-answer diagnostic. This would
  block redeploying a *natively-compiled* LSP server via that closure path,
  not corrupt a running interpreter-mode server.
- `lsp_query.spl` (what the live LSP MCP actually shells out to) runs under
  ordinary `Check`/interpreter mode per S7, so it keeps the **pre-existing**
  sibling-resolution bug the commit was trying to fix — i.e. no regression,
  but also no improvement for LSP from this landing.

## 4. Two-directory drift — confirmed, but currently inert

```
bin/release/linux-x86_64/simple_lsp_mcp_server            94088 bytes  2026-07-23 14:03:50  (ELF, dynamically linked, real binary — just old/small)
bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server 6997688 bytes 2026-07-25 07:44:26
```

The two directories are badly out of sync (2 days apart, ~70x size
difference). Per `.claude/rules/code-style.md`, this drift is billed as "the"
redeploy hazard. In practice today it is **not currently live-hazardous**:
`.mcp.json`'s `simple-lsp-mcp` entry sets no `SIMPLE_PLATFORM_TRIPLE`
(`.mcp.json` env block for `simple-lsp-mcp` lists only `SIMPLE_LOG`,
`RUST_LOG`, `SIMPLE_LIB`, `SIMPLE_EXECUTION_MODE`,
`SIMPLE_LSP_MCP_PREFER_NATIVE`), so the wrapper's
`platform_dir="${SIMPLE_PLATFORM_TRIPLE:-x86_64-unknown-linux-gnu}"`
(`bin/simple_lsp_mcp_server:24`) defaults to `x86_64-unknown-linux-gnu` — the
correct, up-to-date directory. **The stale `linux-x86_64` copy is dead code
under the current `.mcp.json`.** It would only matter if something sets
`SIMPLE_PLATFORM_TRIPLE=linux-x86_64` (a manual macOS/alt-platform override or
future config change) — worth a follow-up cleanup or delete, but not an
active redeploy risk today.

## 5. Unexpected finding: `bin/simple` is currently the Rust seed, not the self-hosted binary

`bin/simple` is a symlink to `bin/release/x86_64-unknown-linux-gnu/simple`
(145,290,352 bytes, mtime `2026-07-27 22:06`). Running `bin/simple --version`
prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

This is exactly the binary `find_simple_binary()` /
`_mcp_find_simple_binary()` resolve to (both check
`bin/release/x86_64-unknown-linux-gnu/simple` before any other candidate —
`src/app/mcp/main_lazy_query_tools.spl:66-79`). So every live `run_lsp_query`,
`run_diagnostics_query`, and MCP CLI-passthrough call is currently executing
against the **Rust seed**, per `.claude/rules/bootstrap.md`'s own rule that
this is bootstrap-only and "NEVER use it as the normal tool." This is
consistent with recorded memory of prior "seed-clobbered" incidents (see
`project_simple_startup_deleted_live_o_tmp_2026-07-26.md`,
`reference_seed_native_build...2026-07-25.md`) and appears to be a
**pre-existing, separate condition**, not something today's HIR/driver/parser
commits caused — those commits live in `.spl` source that only takes effect
once compiled into a redeployed **self-hosted** `bin/simple`, and this one is
Rust-compiled.

Net effect for this investigation: it *further* bounds today's blast radius
(the seed can't have compiled in `.spl`-only changes at all), but it is an
independent finding worth its own follow-up — LSP/MCP query results (diagnostics,
go-to-definition) are currently backed by the degraded seed tool, not the
project's intended default.

---

## Pre-redeploy checklist (do these BEFORE anyone rebuilds/redeploys the
servers or restores `bin/simple` to the self-hosted binary)

1. **Confirm which binary is about to become live.** `bin/simple --version`
   — if it still prints the "Rust-built... bootstrap seed only" warning after
   a rebuild, the redeploy did not produce what was intended; stop.
2. **Cheap driver probe (no build, no link — from the review's own
   recommendation, `review_canonicalization_2026-07-27.md:245-263`):**
   ```
   SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 SIMPLE_NATIVE_BUILD_ENTRY=src/app/cli/bootstrap_main.spl \
     <self-hosted simple> --check src/app/cli/bootstrap_main.spl 2>&1 | grep 'phase2:parse:closure:sources'
   ```
   Expect `collected≈1723, unique=1303` pre-change or `collected≈3030,
   unique=1303` post-change; any `unique > 1303` means aliases are leaking
   into Phase 3 (duplicate-lowering regression) — do not proceed.
3. **Symlinked-entry check** (settles S3): run the same `--check` against
   `src/app/lsp/main.spl` or `src/app/lsp/server.spl` and grep for a missing
   `__simple_main` / entry-module-name mismatch before attempting any native
   AOT build of the LSP server through the entry-closure path.
4. **Two concrete LSP smoke requests** against the rebuilt
   `simple_lsp_mcp_server` before trusting it: `textDocument/definition` and
   `textDocument/diagnostics` (or the MCP tool equivalents
   `lsp_definition` / `lsp_diagnostics`) on a file reachable through a
   symlinked tree (`src/app/lsp/*.spl` or `src/app/spostgre/*.spl`) — these
   are exactly the paths S2 says get an amputated canonical name.
5. **Two concrete MCP smoke calls**: `simple_search` on a symbol defined in
   one of today's changed files (e.g. a symbol in
   `driver_source_loading.spl`), and one CLI-passthrough tool that runs
   `simple check` or `simple lint` on a small `.spl` file, to confirm the
   subprocess target is the intended binary (cross-check with step 1's
   `--version` output, since the passthrough tools silently swallow which
   binary they picked).
6. **Redeploy hygiene per `.claude/rules/code-style.md`:** after any rebuild,
   re-copy natives from `bin/release/x86_64-unknown-linux-gnu/` to
   `bin/release/linux-x86_64/` (or set `SIMPLE_PLATFORM_TRIPLE` consistently)
   so the two directories don't drift further — confirmed today they are
   already 2 days / ~70x apart.

---

## Evidence log

- `git log --since="2026-07-27 00:00" --oneline --name-only` — today's commit list and files.
- `git show --stat` on `8af2dc55596`, `67024e9c0a5`, `559832a135b`, `584e74ece31`, `3eea09c6796`, `e0f6d761320`.
- `.mcp.json` — server launch commands/env.
- `ls -la bin/release/x86_64-unknown-linux-gnu/simple*`, `ls -la bin/release/linux-x86_64/`.
- `ps aux | grep -iE 'simple(_lsp)?_mcp_server|simple_pipe|src/app/mcp/main.spl'`.
- `bin/simple_lsp_mcp_server:24,145-168` (wrapper exec logic).
- `doc/09_report/review_canonicalization_2026-07-27.md` (full read; S2, S3, S7 cited above).
- `grep -rln '20\.hir\|hir_lowering\|driver_source_loading\|80\.driver\|10\.frontend\|parser_decls_use' src/app/mcp src/app/simple_lsp_mcp` and follow-up line-level greps.
- `src/app/mcp/main_lazy_query_tools.spl:66-` (`_mcp_find_simple_binary` candidate order).
- `bin/simple --version` output (trivial invocation, not a build).
