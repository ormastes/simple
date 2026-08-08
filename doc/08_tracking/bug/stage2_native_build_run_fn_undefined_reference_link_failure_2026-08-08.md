# Stage-2 native-build link failure: undefined reference to `run_fn` in `CompilerDriver.process_sdn`

Date: 2026-08-08
Status: OPEN
Area: compiler / codegen / driver (`src/compiler/80.driver/`), native-build link step
Severity: BLOCKER — surfaced on the critical path to verifying
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`; Stage 3
self-host cannot be reached while Stage 2 fails to link.

## Discovery context

Found today while re-running `--full-bootstrap --deploy` to verify the
nil-receiver SIGILL fix, after three prior blockers ahead of it in the same
pipeline were fixed and landed in sequence:

1. `unresolved type: ByteOrder` in `cache_validator.spl` — fixed, `9ad6aea9d349`.
2. Unqualified `case Str:`/`case Bool:`/`case Struct | Enum:` match arms
   (irrefutable-binding hazard) across 4 files — fixed, `a6f0814f38dd9`.
3. A sibling unqualified `case Variable:` instance in
   `src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl` (lines 381,
   644) — fixed, part of `10718083340`.

With all three cleared, Stage 2 native-build progressed past HIR compile into
codegen/link, then failed with:

```
undefined reference to `run_fn' in compiler__driver__driver__CompilerDriver.process_sdn (mod_518.o)
clang++: error: linker command failed with exit code 1
```

This is a **link-time** failure, not a compile-time one — the object file
`mod_518.o` (compiled from `CompilerDriver.process_sdn` in
`src/compiler/80.driver/driver.spl` or a closely related module) references a
symbol `run_fn` that no object file in the link set defines. Not yet
established whether:

- `run_fn` is a genuine function that exists in `.spl` source but whose
  codegen emission is being skipped/miscompiled for this build configuration
  (native-build path), or
- it's a leftover reference to a renamed/removed function (see the "Incomplete
  cross-session rename" pattern already seen once today in a different file —
  `reference_incomplete_cross_session_rename_broke_stage2_mailbox` in project
  memory), or
- it's a closure/function-value lowering gap where a named function used as a
  value doesn't get a matching top-level symbol emitted.

## Repro

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=<path outside repo tree> --progress
```

(The two debug env vars are unrelated to this bug — carried over from the
SIGILL investigation this blocks — but are harmless to leave set.) Full run
takes ~30 min once the Rust seed is already built (cargo rebuild only needed
once). Write output outside the repo tree; disk was at ~97% used / ~119G free
at last check — do not run `git prune`/`git gc --prune` (other lanes have
uncommitted work anchored as loose objects).

## Next steps

- Grep for `run_fn` definition site(s) in `.spl` source and compare against
  what the native-build codegen path actually emits for that build
  configuration — establish which of the three hypotheses above is correct
  before attempting a fix.
- Check `git log -p` / `git blame` on the defining file for a recent rename or
  deletion touching `run_fn`.
- Once root-caused, land the fix in `.spl` only (never a Rust-seed
  workaround), verify Stage 2 links cleanly, and re-run the nil-receiver SIGILL
  verification this blocker was found while chasing
  (`doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`).
