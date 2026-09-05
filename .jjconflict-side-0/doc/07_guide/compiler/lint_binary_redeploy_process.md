# Redeploying the lint oracle (`bin/simple lint`) — process and staleness probe

WP-3.5 of `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`.
Written 2026-08-07 after proving `bin/simple lint` runs a binary older than its
own pure-Simple source.

## The problem in one line

`bin/release/x86_64-unknown-linux-gnu/simple` (what `bin/simple` symlinks to,
and what `bin/simple lint` executes) contains the diagnostic-code string
`MEXH001` but not `MEXH006`
(`src/compiler/90.tools/lint/_LintMain/lint_checks.spl:65`), and not
`W-MC-RES-001`
(`src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`). Every
lint-based check landed against pure-Simple source this session exists in
source but fires for nobody running `bin/simple lint` today.

## Root cause: it's not just stale, it's the wrong binary family

`bin/release/x86_64-unknown-linux-gnu/simple --version` prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-beta
```

That is the **Rust seed** banner. `MEXH001` lives in
`src/compiler_rust/compiler/src/lint/types.rs` (Rust) as well as in the
pure-Simple `lint_checks.spl` — that is why it shows up in the binary at all.
`MEXH006` and `W-MC-RES-001` are pure-Simple-only diagnostics that were never
ported to the Rust seed's lint implementation. **No redeploy of pure-Simple
lint source can ever make them appear in a seed binary**, no matter how it is
rebuilt — they can only appear in a genuinely self-hosted Stage-3 binary.

The deployed file is also not literally the checked-in bootstrap seed
(`src/compiler_rust/target/bootstrap/simple`, 33 MB, md5 `0ae349d3...`) — the
deployed `bin/release/x86_64-unknown-linux-gnu/simple` is 58 MB, md5
`ecefd148...`. It is a separately-built Rust seed binary (see
`.claude/rules/bootstrap.md`'s warning about hand-rolled
`cargo build --release` copies masquerading as deployed binaries), not a
self-hosted one either way.

## Correct redeploy procedure (per `.claude/rules/bootstrap.md`)

1. **Never** hand-roll `cargo build --release` and copy the result to
   `bin/release/<triple>/simple`. That produces a fresh seed with a
   deceptively fresh mtime, not a self-hosted binary, and resets the
   staleness clock for the next session without fixing anything.
2. The documented, repeatable command is:
   ```bash
   scripts/bootstrap/bootstrap-from-scratch.sh --deploy
   # or, if the Rust seed/runtime itself also needs a rebuild:
   scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy
   ```
   This runs Stage 1 (seed) → Stage 2 (seed compiles pure-Simple) → Stage 3
   (the freshly-built Stage-2 compiler recompiles itself — the actual
   self-host proof) → deploy, and refuses to fall back to the seed for the
   full CLI build if Stage 3 doesn't pass.
3. Verify tier: per `.claude/rules/bootstrap.md`'s T0–T3 ladder, a change
   under `src/compiler` (which `90.tools/lint` and `35.semantics/lint` both
   are) requires **T3 — full bootstrap**. There is no cheaper tier that
   produces a binary containing pure-Simple-only lint diagnostics, because
   the deployed artifact must itself be pure-Simple-compiled.
4. Known launch-path skew: `.mcp.json` launches `simple-lsp-mcp` (and by the
   same convention, tooling expects) binaries from `bin/release/linux-x86_64/`
   (gitignored), while builds deploy to
   `bin/release/x86_64-unknown-linux-gnu/`. After a real redeploy, re-copy to
   the launch path — direct `cp` over a running binary hits "Text file busy",
   so use the `cp <path>.new` + `mv <path>.new <path>` dance
   (`.claude/rules/code-style.md`, `doc/07_guide/app/mcp/mcp.md` §
   Troubleshooting).

## Status as of 2026-08-07: T3 full bootstrap is blocked, not merely slow

A same-day investigation (`doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`)
ran `--full-bootstrap --deploy` for real. Stage 1/2 passed. Stage 3
(self-host) failed. The first blocker (`unresolved type: ByteOrder` in
`cache_validator.spl`) was fixed and reproduced clean via a pinned-worktree
replay (RED exit 1 → GREEN exit 139 further along → re-sabotage RED exit 1).
Past that wall, Stage 3 now dies **later and differently**: a SIGSEGV (exit
139, "dumped core") during `phase=monomorphize` / MIR lowering, ~394s wall,
peak RSS 10.7 GB, with no diagnostic — a signal, not an error line. That is a
distinct, still-open defect from the one just fixed, and from two other
already-catalogued Stage-3 failure modes (stack overflow, non-termination).

This is a genuine, actively-investigated open compiler bug — not a tooling
gap and not something this WP can shortcut. Per this session's own guidance
("no bootstrap unless essential" balanced against "if it's taking many hours
with no progress, stop and report"), WP-3.5 does not re-attempt the T3 replay:
prior sessions already spent multiple hours reaching and confirming this
exact wall today. Re-running it would reproduce the same SIGSEGV, not resolve
it — resolving it is Stage-3's own open bug, tracked separately.

**Practical consequence:** until that Stage-3 MIR-lowering SIGSEGV is fixed,
*no* pure-Simple source change — lint-related or otherwise — can be deployed
to `bin/simple` via the documented, non-shortcut path. This is broader than
lint; it blocks every 🟡/🔴 WP in Wave 2 that needs to observe its own fix
through the deployed binary.

## The staleness probe

`sh scripts/check/check-lint-binary-staleness.shs [binary-path]` — mechanical,
grep-only, no build. Checks a binary (default: the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`) for two fresh pure-Simple-only
markers (`MEXH006`, `W-MC-RES-001`), after first confirming both still exist
in current source (fail-closed on a renamed diagnostic code — reports `ERROR`,
not a stale `FAIL`, if the premise itself breaks).

Verdict is always the last stdout line: `PASS — ... / FAIL — ... / ERROR — ...`,
exit 0/1/2. `--selftest` proves the PASS branch isn't dead code by running the
same logic against synthetic fresh/stale fixtures, without requiring a real
redeploy.

Every later WP in this plan should run this probe first; per the plan's
amendment, a WP that cannot prove it ran against a fresh binary reports its
result as unverified, not as pass.
