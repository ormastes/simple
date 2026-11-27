# Bootstrap erased-text `rfind` loses Optional not-found semantics
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

RESOLVED 2026-11-25 — the `-1` vs `nil` mismatch no longer exists: the
language contract for `rfind`/`last_index_of` was corrected to plain `i64`
with `-1` for not-found, so the bootstrap fallback matches the contract.
See the dated verification note at the bottom. (Formerly: Open, tracked by
TODO 559.)

## Problem

The pure-Simple Stage4 bootstrap MIR fallback for an unresolved erased-text
receiver now selects the canonical `rt_string_rfind` runtime owner. That ABI
returns `-1` when the needle is absent, while the language API is `i64?` and
normally exposes `nil` for absence. The current full-CLI closure only coalesces
the result before comparing it, so restoring the owner fixes linking without
changing that caller, but the fallback is not a general semantic solution.

## Required fix

Preserve the receiver and method-result type through HIR/MIR so normal text
method lowering owns `replace(...).rfind(...)`, or adapt the runtime result into
the canonical Optional representation. Add executable found and missing-needle
coverage before removing TODO 559. Do not add a second runtime string-search
owner or a caller-specific constant.

## Verification 2026-11-25 (p2w1-ag lane, source inspection)

RESOLVED by contract alignment — the defect's premise is gone. This entry was
filed on the basis that "the language API is `i64?` and normally exposes `nil`
for absence", so the MIR fallback's `-1` was a semantic mismatch. The language
contract has since been deliberately corrected to plain `i64` with `-1` for
not-found, everywhere:

- `src/lib/text.spl:53` declares `extern fn rt_string_rfind(s: text, needle: text) -> i64`;
  `src/lib/text.spl:74` declares `fn last_index_of(s: text, needle: text) -> i64`
  with a doc comment spelling out the raw-i64/`-1` contract and why.
- The MIR fallback comment at
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:5069-5078`
  records the correction: "That IS the language contract ... there is no
  -1-vs-nil mismatch here at all. Callers must test `>= 0`, not nil."
- The contract is consistent across runtime.h, runtime_native.c,
  collections.rs, runtime_sffi.rs, core_string.spl and common/string_core.spl
  (per the same comments).

Found and missing-needle coverage exists:
`test/01_unit/language/nil_presence_idioms_spec.spl:182-186`
(`last_index_of` returns -1 when the needle is absent, plus found cases),
`test/01_unit/language/text_index_branches/text_len_slice_native_adr005_spec.spl:76-78`
(found offsets), and the native fixture
`test/fixtures/text_search_index_abi_native/main.spl:43-44` (`rfind` /
`last_index_of` found-needle at the runtime boundary).

Verified by source inspection only: spec execution at this HEAD is blocked
repo-wide by the pinned seed rejecting `@representation_boundary`
(release/1.0.0 source/binary inconsistency, known issue). Residual
bookkeeping: TODO 559 is still referenced from
`.spipe/simpleos-qemu-host-gpu-2d/state.md` and
`doc/08_tracking/bug/native_build_stage4_pre_object_spin_2026-07-13.md`; the
"preserve receiver type through HIR/MIR" item is a compiler design nicety,
not a defect, now that fallback and contract agree.

