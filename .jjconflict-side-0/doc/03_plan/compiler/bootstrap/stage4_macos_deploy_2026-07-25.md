# Stage4 macOS full-CLI deploy — COMPLETE 2026-07-25

**Status:** DEPLOYED. `bin/simple` → `bin/release/aarch64-apple-darwin-macho/simple`
now runs the stage4 full-CLI self-hosted binary built from main `4ed680f5` by the
fixed seed. Redeploy gate **11/11 PASS** on the live path; MCP stdio handshake
green; `simple test` executes current-main specs (the Jul-5 incumbent could not —
`unknown extern function: rt_process_spawn_guarded`). Backups:
`simple.bak-2026-07-25` beside both `bin/release/aarch64-apple-darwin{,-macho}/simple`.

## Build recipe (canonical)

1. Seed: `cargo build --profile bootstrap -p simple-driver`, then
   `-p simple-compiler-backfill` (stage4 links
   `target/bootstrap/libsimple_compiler_backfill.a`; stale = old extern registry,
   "unknown extern function" at call time), then ALWAYS LAST
   `CARGO_PROFILE_BOOTSTRAP_LTO=off cargo build --profile bootstrap -p simple-runtime
   --features runtime-symbol-table` (machine-code exports win the deps/ slot).
   All three steps are in `scripts/bootstrap/bootstrap-from-scratch.sh`.
2. Stage4: seed binary + `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1
   SIMPLE_NO_STUB_FALLBACK=1`, `--runtime-bundle core-c-bootstrap --entry-closure`,
   sources from a worktree tracking CURRENT main (stale worktree ⇒ C-core/codegen
   API skew ⇒ value-ABI split). Wipe the content-keyed object cache after any
   codegen-affecting seed change — it does NOT fold in the seed fingerprint.
3. Deploy: gate ≥ incumbent, MCP probe, dated `.bak`, cp-to-`.new`+`mv`, refresh
   the `simple_seed` sibling (delegation target) in the SAME dir, and verify via
   the ABSOLUTE binary path.

## Seed defects fixed this arc (all pushed)

vtable owner fallback; win32/memtrack/spl_str_ptr providers; objcopy newest-llvm;
dead-strip liveness trial link; Cocoa ObjC provider; `-r`-mode reference-object
seeding (Apple ld ignores `-u` there); no-LTO runtime ordering; undefined-trait
vtable consistency (`trait Backend` exists nowhere — bug filed) + empty-slot
emission; string-builtin mangler guard hoisted pre-resolution (scoped: enum/
numeric lists stay post-failure); main-stub contract symbols kept global in the
C capsule (argv was never captured); **Result/Option builtin-helper dispatch
misbinding** (substring match bound `Result.is_err` → `FailSafeResult.is_err`,
`unwrap` → `Poll.unwrap` returning 0 — every interpreted Value became NULL);
**string literals emitted as stack slots then interned by (address,len)** — two
same-length literals aliased ("simple_seed" → "--log-mode=") — now real rodata
via `declare_named_bytes`.

## Residual (filed, non-blocking)

- `bin/simple` on macOS is a local exec wrapper (absolute argv0): the compiled
  CLI's relative-argv0 exe-path branch still corrupts values (cwd()-chain);
  root-fix belongs in `src/app/io/cli_ops.spl` exe-path resolution (no
  /proc/self/exe on macOS). Re-running `scripts/setup/setup.shs` recreates the
  symlink and reintroduces the broken lane — re-apply the wrapper.
- In-process interpreter gaps when delegation is unavailable: no
  `HirExprKind.NullCoalesce` eval arm; flat-bridge interpolation sub-parse;
  Value `==` on Ints — peer interpret-lane workstream.
- Parity defects (also in old binary): struct-copy aliasing, `i64? ??` float-zero,
  `!!` payload loss — `doc/08_tracking/bug/interp_option_struct_semantics_macos_parity_2026-07-25.md`.
- Dispatch hardening: segment-boundary matching in
  `codegen/instr/closures_structs.rs:544`; type-qualified Result./Option. guard.
