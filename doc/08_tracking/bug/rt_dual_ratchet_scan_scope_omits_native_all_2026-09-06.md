# `check-rt-dual-implementation-ratchet.shs` does not scan `src/compiler_rust/native_all`

- **Filed:** 2026-09-06
- **Class:** ratchet scope hole — false single-lane classification
- **Status:** open. Confirmed and measured; deliberately NOT fixed here (see
  "Why not widened").

## Claim

The guard's Rust lane is exactly `src/compiler_rust/runtime/src/**/*.rs`
(`extract_lanes`). Two other directories define `#[no_mangle] pub extern "C" fn
rt_*` runtime providers and are invisible to it:

- `src/compiler_rust/native_all/src/`
- `src/compiler_rust/native_loader/src/`

A symbol whose only Rust definition lives there is reported as *not present in
the Rust lane*. Depending on the C side that produces either a false `c-only`
row or — worse — a false **stale** verdict, because the guard sees the symbol in
neither lane and concludes the baseline row no longer describes the tree.

## Confirmed instance

`rt_phase_profile_record`. Baselined `rust-only`. PR #271 (`5e09b3ef2fd`,
"unify duplicated rt_mem_snapshot_* Rust providers") moved it out of
`src/compiler_rust/runtime/src` and into
`src/compiler_rust/native_all/src/mem_snapshot_provider.rs:363`, where it still
is. Its Rust lane never disappeared; only the guard's view of it did.

```sh
grep -rn 'fn rt_phase_profile_record' src/compiler_rust/
#   src/compiler_rust/native_all/src/mem_snapshot_provider.rs:363
sh scripts/check/check-rt-dual-implementation-ratchet.shs   # reports it STALE
```

The row was removed on 2026-09-06 to clear the blocking gate. That removal is
correct **only under the guard's current scope** and is annotated as such in
`scripts/check/rt_dual_implementation_baseline.txt`. If the scope is widened the
row must come back as `rust-only`.

## Measured blast radius of widening to `native_all` + `native_loader`

22 `rt_*` definitions live there. Against the current tree:

- **9 already defined in `runtime/src`** — no change
  (`rt_array_new`, `rt_cli_run_file`, `rt_interp_call`, `rt_mem_snapshot_close`,
  `rt_mem_snapshot_open`, `rt_mem_snapshot_record`, `rt_println_value`,
  `rt_value_int`, `rt_vk_device_create_for_window`).
- **1 would flip `c-only` -> dual**, i.e. become a NEW stale row: `rt_hostname`.
- **12 would become rust-only**, of which 11 are not baselined at all and would
  land as NEW single-lane debt: `rt_cargo_fmt`, `rt_cargo_lint`,
  `rt_cargo_test_doc`, `rt_current_time_ms`, `rt_execute_native`,
  `rt_get_concurrent_backend`, `rt_jit_cleanup`, `rt_native_build`,
  `rt_run_tests`, `rt_set_concurrent_backend`, `rt_system_cpu_count`
  (`rt_phase_profile_record` is the twelfth and is already baselined).

## Why not widened here

Widening is not obviously the right fix, and doing it under gate pressure would
be the wrong way to decide.

The guard's stated subject is "every `rt_*` **runtime primitive** should have a C
implementation AND a Simple implementation". Most of the 11 would-be-new symbols
are not runtime primitives: `rt_cargo_fmt`, `rt_cargo_lint`, `rt_cargo_test_doc`,
`rt_native_build`, `rt_run_tests`, `rt_execute_native` are driver/CLI
orchestration hooks, which is precisely why they live in `native_all` rather than
in the runtime crate. Importing them into a runtime-primitive ratchet would add
11 rows of noise and change what the ratchet means.

Do NOT "fix" this by regenerating the baseline. The scope question has to be
answered first: either

1. widen the Rust lane to `native_all` + `native_loader` and admit the 11 with
   per-symbol justification, plus resolve `rt_hostname`; or
2. keep the scope and state in the guard's header that `native_all` /
   `native_loader` are deliberately out of the runtime-primitive population — in
   which case the guard should *detect* an `rt_*` that exists only there and
   report it distinctly, rather than silently classifying it as missing.

Option 2 is the smaller, more honest change and is the recommended one: it turns
a silent misclassification into a named category. Either way the guard currently
reports at least one symbol wrongly, and a ratchet that mislabels its own
population will keep producing phantom stale rows every time a provider moves
between crates.

## Reproduction

```sh
sh scripts/check/rt-dual-implementation-census.shs   # nm-based, authoritative
grep -rhoE '\bfn[[:space:]]+rt_[A-Za-z0-9_]+' \
  src/compiler_rust/native_all/src src/compiler_rust/native_loader/src \
  | grep -oE 'rt_[A-Za-z0-9_]+' | sort -u      # the 22 invisible definitions
```

Note the census script reads DEFINED symbols out of real link artifacts via
`nm` and is the authority on the population; the divergence between it and the
gate's text globs is exactly the error bar this hole widens.
