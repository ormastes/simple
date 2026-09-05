# gen-lean CLI Infinite Recursion — Rust codegen unreachable - 2026-06-30

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
