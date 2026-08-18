# gen-lean CLI Infinite Recursion — Rust codegen unreachable - 2026-06-30

Status: RESOLVED 2026-08-17 (verified by EXECUTION). The recursion is gone AND a
second, newly-exposed blocker was fixed in this pass.

Binary: `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(59537240 bytes, 2026-08-17 12:58:51 UTC).

**1. Recursion: gone.** `timeout 90 bin/simple gen-lean compare` TERMINATES. The
bootstrap-seed banner appears exactly **2** times in the combined output
(`grep -c 'bootstrap seed only'` -> 2), i.e. the wrapper performs a SINGLE
delegation hop, not an unbounded chain. `bin/simple gen-lean --help` exits 0 and
prints the real usage text.

**2. Newly exposed blocker, fixed here.** With recursion gone, the delegated
process reached `src/compiler/90.tools/verify/main.spl` and died with
`error: runtime: Module "io" does not export 'fs'` — a stale
`import io.fs as fs` whose only use was `fs.exist(path)`. Fixed in pure Simple:
`use std.io.{file_exists}` / `file_exists(path)`
(`src/lib/nogc_sync_mut/io/file_ops.spl:64`, exported at
`src/lib/nogc_sync_mut/io/__init__.spl:107`).

**3. Rust codegen is now reachable from the CLI** — the exact claim this bug said
was impossible:

```
$ bin/simple gen-lean compare 2>/dev/null | head -30
  [1/15] regenerate_nogc_compile...
    step 1: LeanCodegen.new
    ...
    step 15: emit
  [2/15] regenerate_async_compile...
  ...
  [15/15] regenerate_tensor_memory...
$ bin/simple gen-lean compare >/dev/null 2>&1; echo $?
1
```

All 15 inventory projects are generated and compared. Exit 1 is the legitimate
compare-mismatch verdict (generated output differs from the checked-in Lean
files), not the recursion failure. The "Secondary limitation" section below
(fixed 15-project inventory) is unchanged and remains a design scope limit.

## Status

Open. `bin/simple gen-lean <sub>` does not run; the Simple→Lean generation CLI is
unusable from the command line. Worked around (not blocked) for the NVMe firmware
proofs by hand-transcribing the mirror defs under a marked `gen lean` section — see
`doc/07_guide/compiler/lean_verification_workflow.md` § "Generated-Mirror / Manual-Proof Split".

## Summary

`bin/simple gen-lean` dispatches to the pure-Simple wrapper `src/app/gen_lean/main.spl`,
which is a thin delegator: it parses log options and then re-invokes `./bin/simple gen-lean <args>`
via `rt_process_run` (`delegate_gen_lean`). Because the spawned process re-enters the **same**
wrapper, the command recurses without bound — `./bin/simple gen-lean gen-lean … <sub>` — and the
Rust codegen handler `run_gen_lean` (`src/compiler_rust/driver/src/cli/gen_lean.rs`) is **never
reached** through the CLI.

## Mechanism (root cause)

1. `"gen-lean"` is listed in `command_is_pure_simple_tool` (`src/compiler_rust/driver/src/main.rs`).
   So `dispatch_command` takes `pure_simple_tool = true` and **skips** the
   env-override → Rust-handler branch (the `SIMPLE_GEN_LEAN_RUST` override at the `gen-lean`
   COMMAND_TABLE entry is therefore dead — setting it still recurses), routing to
   `dispatch_to_simple_app` (the wrapper) instead.
2. The wrapper `src/app/gen_lean/main.spl` `delegate_gen_lean` builds `["gen-lean"] + args` and
   runs `rt_process_run("./bin/simple", forwarded)` — re-entering step 1.

The Rust codegen is reachable today only by internal callers
(`src/compiler_rust/driver/src/cli/verify.rs` invoking `["gen-lean","write","--force"]` /
`["gen-lean","verify"]` in-process), not via the user-facing command.

## Secondary limitation (design, not a regression)

Even when reached, `generate|write|compare|verify` operate on a **fixed inventory** of
`src/compiler_rust/lib/std/src/verification/regenerate/*.spl` modules (the 15 supported
projects). They do **not** scan arbitrary `@verify` user files; only
`gen-lean memory-safety --file <p>` consumes an arbitrary `.spl`, and only for memory-safety
obligations. So algorithm-level Lean for code outside that inventory (e.g. the NVMe
firmware/emulator) cannot be machine-generated regardless of the recursion bug.

## Fix options

- Remove `"gen-lean"` from `command_is_pure_simple_tool` so the env-override → Rust-handler
  branch fires (run `run_gen_lean` directly); **or**
- Make `delegate_gen_lean` call the Rust handler path instead of re-spawning `./bin/simple`
  (e.g. a distinct internal subcommand token the wrapper forwards once and the dispatcher
  routes to Rust without re-listing it as a pure-Simple tool).

Either requires rebuilding + redeploying the Rust seed (the shared `bin/simple`), so it is a
compiler-tooling change, out of scope for an example/firmware lane.

## Reproduction

```sh
# Recurses (observed via strace as an unbounded ./bin/simple gen-lean gen-lean … chain);
# do not run unguarded — it spawns until killed.
bin/simple gen-lean compare
```

## Impact

- The documented `simple gen-lean generate|write|compare|verify` workflow does not run.
- `simple verify check` (which shells `gen-lean` internally via verify.rs) is affected on the
  same path.
- Example/firmware Lean proofs use hand-transcribed mirror defs (marked `gen lean` sections)
  verified by raw `lean <file>`; this is unaffected by the bug.
