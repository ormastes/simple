# Bug: `rt_file_read_lines` / `rt_current_dir` returned `Option`-wrapped
# values where every real `.spl` caller declares a plain, non-optional
# return type — FIXED

**Date:** 2026-07-18
**Lane:** N3 (parallel bug-fix campaign), worktree `wt_n3` detached at
`origin/main` (tip `7ca8f264f3c` at investigation time).
**Severity:** P3 — latent (no currently-live caller trips it), same
mechanism class that broke native-build for `rt_file_read_bytes`.
**Status:** Fixed for `rt_file_read_lines` and `rt_current_dir`.
`rt_file_read_bytes` itself is **already fixed elsewhere** (see "Related /
not touched here" below) — NOT re-touched by this change.

## Summary

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs` had three
functions wrapping their return value in `make_some(...)`/`make_none()`
(an `Option::Some`/`None` enum) even though every real `.spl` `extern fn`
declaration for them uses a plain, non-optional return type and every real
caller consumes the result directly (no `Some(...)`/`None` unwrap):

1. `rt_file_read_lines` — declared `-> List<text>` / `-> [text]` in
   `src/compiler_rust/lib/std/src/infra/file_io.spl`,
   `src/lib/nogc_sync_mut/ffi/io.spl`, `src/lib/nogc_sync_mut/sffi/io.spl`.
   This is the exact function flagged (but left unfixed, "no `.spl` entry
   point currently reaches it") in P3's
   `native_build_fresh_seed_optionwrap_landmine_2026-07-18.md`, item 3:
   *"`rt_file_read_lines` (`file_io.rs`, two functions above
   `rt_file_read_bytes`) still returns `make_some(...)`/`make_none()` ...
   worth the same audit if it ever surfaces."* This is that audit.
2. `rt_current_dir` — declared `-> text` in
   `src/compiler_rust/lib/std/src/infra/file_io.spl` (`current_dir()`,
   plain passthrough). Not mentioned in P3's doc; found while auditing
   `file_io.rs` for the same latent-bug class. A sibling function,
   `rt_get_cwd`, was added right below it explicitly as "returns plain
   text, for snpm compatibility" — i.e. the codebase already worked around
   this bug once by adding a duplicate function instead of fixing the
   root, rather than fixing `rt_current_dir` itself.

Both mirror the mechanism that broke native-build for `rt_file_read_bytes`:
an interpreter-only extern binding returning an `Option`-wrapped enum when
the compiler's own type declarations (and every real consumer) expect a
bare value. If a caller ever consumed either of these two functions the way
`llvm_backend_tools.spl` consumed `rt_file_read_bytes`, it would hit the
same `unknown static method object on class CodegenOutput` / "cannot
convert object to int" class of failure.

## Fix

`src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`:

- `rt_file_read_lines`: returns bare `Value::array(...)` on success,
  `Value::Nil` on failure (was `make_some(Value::array(...))` /
  `make_none()`).
- `rt_current_dir`: returns bare `Value::text(...)` on success,
  `Value::text(String::new())` on failure (was
  `make_some(Value::text(...))` / `make_none()`), matching the fallback
  already used by the `rt_get_cwd` workaround.

No `.spl` call site needed a consumer-side change for either function:
grepped every `rt_file_read_lines`/`rt_current_dir` extern declaration and
call site in `src/`; all declare a plain (non-optional) return type and
consume the result directly, with zero `match ... Some(...)/None` or
`?? ...` consumers found for either.

`rt_get_cwd` (the pre-existing workaround) was left as-is — it already
returns a bare value and removing the duplicate is out of scope for this
fix.

## Regression tests

Added to the existing `#[cfg(test)] mod tests` block in `file_io.rs`:

- `read_lines_returns_bare_array_not_option_wrapped` — reads a 3-line fixture
  file and asserts the result is `Value::Array` (not `Value::Enum{Option}`)
  with the expected line contents.
- `read_lines_returns_nil_not_option_none_on_missing_file` — reads a
  nonexistent path and asserts the result is bare `Value::Nil`, not
  `Value::Enum{Option, None}`.
- `current_dir_returns_bare_text_not_option_wrapped` — asserts
  `rt_current_dir` returns `Value::Str`, not `Value::Enum{Option}`.

Each test's `match` arm on the *old* code would have hit the `other =>
panic!` fallback (the old code returned `Value::Enum{enum_name: "Option",
...}`), so these are genuine repros, not smoke tests.

## Verification status

**Not run — load discipline.** Repo-wide `cargo build`/`cargo test` was
gated by the DISK+CPU rule for this lane (`load < 15 AND > 30G free`
before building): `uptime` read load average **16.08** right before this
investigation started and **59.83** by the time the fix + tests were
written (other lanes building concurrently). Disk was fine throughout
(~298-301G free). The fix was verified by static review only:
- Diffed against the already-landed, verified sibling fix for
  `rt_file_read_bytes` (commit `fec74762272`, see below) — identical
  shape (`Ok(make_some(x))` → `Ok(x)`, `Ok(make_none())` → `Ok(Value::Nil)`
  / a plain-value fallback).
- Confirmed `Value::text`/`Value::array` constructors and the `Value::Str`/
  `Value::Array`/`Value::Nil` variants used in the new tests match
  `src/compiler_rust/compiler/src/value.rs` exactly.
- Exhaustively grepped every `.spl` `extern fn rt_file_read_lines`/
  `rt_current_dir` declaration and call site (see "Fix" above) to confirm
  no consumer expects `Option`.

**Follow-up required:** once load drops below the lane's build threshold,
run `cargo test -p simple-compiler --lib interpreter_extern::file_io::` to
confirm the three new tests pass and no existing test regresses (none
should — `mmap_named_text_and_bytes_match_read_contract`, the only other
test in this module touching a Option-wrapping contract, exercises
`rt_file_read_bytes`/`rt_file_mmap_read_bytes`, not the two functions
touched here).

## Related / not touched here: `rt_file_read_bytes`

This worktree (`wt_n3`, detached at `origin/main`) does **not** contain
P3's fix — `rt_file_read_bytes` in this tree's `file_io.rs` still returns
`make_some(...)`/`make_none()` at the time of this writing. That fix
already exists, verified and committed, on a separate, not-yet-merged
lane/worktree (commits reachable in this repo's shared git object store
via `git log --all` / `git show <sha>:<path>`, but not ancestors of this
worktree's `HEAD`):

- `fec74762272` / `5b78c592239` — "fix(interpreter): rt_file_read_bytes
  returns bare array, not Option-wrapped" (the `file_io.rs` change itself,
  plus rewriting the two `Some(...)`/`nil` pattern-matching consumers
  `src/lib/nogc_sync_mut/sfm/container.spl` and
  `src/lib/nogc_sync_mut/io/telnet_serial_bridge.spl` to `?? []`, plus
  updating the one Rust test that asserted the old contract).
- `39be711134c` / `ad567dd95ba` — "fix(os/port): finish rt_file_read_bytes
  contract audit, 2 more consumers" (follow-up covering
  `src/os/port/host_fat32_tree_populator.spl` and
  `src/os/port/cached_raw_image_block_device.spl`, two more genuine
  `Some(...)`/`None`-matching consumers found by a broader tree-wide grep).

**Deliberately not reapplied here**, for two reasons:
1. **Scope/merge cleanliness.** Reapplying would mean also editing the same
   four `.spl` consumer files P3's lane already owns, plus the same
   `file_io.rs` hunk — two lanes touching identical lines for no benefit.
   Leaving `rt_file_read_bytes` untouched in this tree means this lane's
   `file_io.rs` changes (to `rt_file_read_lines`/`rt_current_dir`, both
   functions P3's lane never touched) and P3's changes (to
   `rt_file_read_bytes`) are on disjoint functions in the same file → a
   clean merge for the orchestrator.
2. **Contract risk.** Unlike `rt_file_read_lines`/`rt_current_dir` (zero
   `Option`-consumers found for either), `rt_file_read_bytes` genuinely has
   mixed consumers — some declare it plain and consume directly, some
   declare `[u8]?`/`[i64]?` and pattern-match `Some(...)`/`None` directly.
   P3's lane already did the call-site audit and rewrite required to make
   that fix safe; redoing it here from scratch risks diverging from an
   already-verified fix.

When this lane's work is merged with P3's, the orchestrator should confirm
both landed (this doc's fix + P3's `fec74762272`/`39be711134c` chain, or
their eventual equivalents on `main`) and that the shared
`make_some`/`make_none` test coverage in `file_io.rs` reconciles cleanly
(no duplicate/conflicting edits to `mmap_named_text_and_bytes_match_read_contract`).
