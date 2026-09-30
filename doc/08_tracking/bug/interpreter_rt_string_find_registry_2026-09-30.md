# Raw string-find interpreter registration

## Observed release blocker

The fully hydrated release push gate at local commit
`f385a8bc1657c075726e4adf322b9b175da069b1` rejected 238 compiler externs with
one new gap, `rt_string_find`, and one stale baseline entry,
`rt_string_index_of`. Evidence:
`D:/dev/simple-astra-nul-concat-release-20260930/build/native_probe/runtime-concat-nul/push-release-complete-inputs.log`.
Main `0814a6dfa5e` has the same missing registration.

`src/compiler/10.frontend/core/types.spl` declares and calls `rt_string_find`
after the raw-byte-offset correction. The old Rust runtime
`rt_string_index_of` returns a boxed Option and is not interchangeable with
this primitive. The C owner `src/runtime/runtime_native.c` defines find as
the first byte offset, `-1` for no match, and `0` for an empty needle.

## Source correction

The string interpreter owner now implements `rt_string_find_fn` and registers
it in the actual `EXTERN_DISPATCH` table. It returns `Value::Int`, including
`-1` on a miss, rather than nil or an Option. Both interpreter text values and
existing runtime string handles are accepted. Runtime spans are copied as
bytes before resolving the other argument, preserving embedded NUL and
non-UTF-8 bytes without lossy conversion or borrowed-pointer reuse. Wrong
arity and invalid argument types return errors through existing diagnostics.

Only after adding genuine ownership is the stale `rt_string_index_of`
baseline entry removed. No new gap is baselined, no symbol is renamed to
evade the gate, and the registry checker is unchanged.

## Reproduction and prevention tests

Three tests call the real registered handler in `interpreter_extern/mod.rs`:

- `rt_string_find_is_registered_and_returns_raw_byte_offsets`: registration,
  first occurrence, tail hit, miss, longer needle, both empty cases, UTF-8
  byte offsets, and embedded NUL matching.
- `rt_string_find_preserves_runtime_handle_bytes_and_mixed_arguments`:
  runtime-owned bytes, mixed interpreter/runtime arguments, invalid UTF-8
  before a match, raw-byte needles, and empty needles.
- `rt_string_find_rejects_wrong_arity_and_non_text_arguments`: zero, one,
  and three arguments; nil receiver/needle; non-string integer.

At initial source preparation these were authored tests, not execution
evidence. The historical raw-find diagnostic lane had exhausted three
verification cycles, so preparation did not rerun tests or gates. The later
explicitly authorized focused cycle is recorded below. Native-build
delegation cannot qualify these tests.

## SOSIX host-access audit

The handler performs in-memory byte copying and searching only. Runtime
handle extraction uses the existing `simple_runtime::value` string owner
accessors already used by neighboring string handlers. There are no new
filesystem, environment, process, clock, network, or other host operations,
so no SOSIX host-access adapter is needed. Tests use runtime-owned memory
allocation and release only; they add no direct host I/O.

The patch is isolated from the NUL-concat and hook-path commits, frozen
bootstrap sources, and their caches. Main and release source preparation
does not qualify or publish a release.

## Subsequently authorized focused validation

The user authorized one additional focused test-and-gate cycle. The three
registered-handler tests above passed on the unchanged Rust source in
`dc2006f8187aaa6660e670139b9aee6495e9d52a`: 3 passed, 0 failed, 0 ignored,
4249 unrelated tests filtered out. The command used the installed Windows
nightly toolchain, the canonical clang/LLVM environment, an isolated copy of
the Cargo dependency cache, and two build jobs:

`cargo test --offline --locked -p simple-compiler --lib --profile dev rt_string_find_ -- --test-threads=1`

Sparse checkout omissions in the setup helper and a tracked backend header
were restored before any test could execute. The retained-cache build then
completed in 4m 20s; the three named tests ran once and passed. No product
source was changed to accommodate those setup omissions.

The standalone frozen-baseline scan at the same exact commit failed with
220 symbols checked, 10 other new gaps, and 5 stale entries. None involved
`rt_string_find` or `rt_string_index_of`. Static comparison against exact
parent `0814a6dfa5eef7c5acfdb629f5e7cf82ef817dd0` found all 47 declaration,
dispatch, and baseline rows mentioning those 15 symbols unchanged. No
baseline entries were rewritten to hide that inherited debt.

The distinct canonical push check passed with 220 symbols checked and zero
new gaps versus that exact parent:

`sh scripts/check/check-interpreter-extern-registry-gap.shs --scan-only --rev dc2006f8187aaa6660e670139b9aee6495e9d52a --baseline-rev 0814a6dfa5eef7c5acfdb629f5e7cf82ef817dd0`

Evidence is retained under `D:/dev/simple-string-find-review-20260930/`:
`registry-focused-cycle-cargo-resume.log`,
`registry-focused-cycle-gate.log`,
`registry-inherited-debt-source-comparison.json`, and
`registry-focused-cycle-branch-delta.log`. This is focused handler and
branch-delta PASS, not full-suite, frozen-baseline, or release qualification.

## Exact main/release patch portability

The unique registration was moved immediately after `rt_string_free` in the
same dispatch table so the fix has identical surrounding patch context on
main and release. The implementation file and all three registered-handler
test bodies are byte-for-byte unchanged; removing the one registration line
from the before/after dispatch files leaves identical bytes. The already
passing named tests were not rerun for this order-only change.

The rewritten source fix `e4b103087c73d1a3cce76d789b9cdbf170c41257`
applies directly to release base `d921e11599ee94519c9813c4df0ab1ed6e391d70`.
Both default stable patch IDs are
`cbb62dddd98d1b0b73af082feefcb080683c3639`. The four-file release preview
is unadmitted and does not move a protected ref. The prior PR head/review is
superseded and the new head requires fresh protected checks and review.
