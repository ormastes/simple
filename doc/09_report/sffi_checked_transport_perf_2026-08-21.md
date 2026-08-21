# SFFI checked transport performance evidence

Date: 2026-08-21

Revision under test: worktree successor to `1ab58bd9962`

## Regression found and removed

The first checked-transport increment made legacy
`spl_wffi_call_i64` allocate a temporary runtime array on every call. The
implementation now delegates to the allocation-free stack-only
`try_call_i64_value`; `spl_wffi_call_f64` uses the equivalent float helper.

## Static hot-path gate

`scripts/audit/sffi-null-signature-guard.shs` extracts both legacy function
bodies and fails if either contains `rt_array_new`, `Vec`, `HashMap`, `Mutex`,
or `dlsym`. This protects the existing performance-sensitive LLVM/GPU callers
from reintroducing allocation, locking, or symbol lookup per call.

## Assembly evidence

Debug shared-library disassembly after the fix shows:

- `spl_wffi_call_i64`: one call to `try_call_i64_value`, status test, conditional
  move, return;
- `spl_wffi_call_f64`: one call to `try_call_f64_value`, status test, result
  move, return;
- neither wrapper calls array allocation, symbol lookup, hashing, or locking.

The checked pair-returning adapters allocate their two-element result because
the interpreter value model cannot mutate caller arrays. They are migration and
development-plugin APIs, not the final production hot path. Static/sealed
providers must use generated typed thunks with cached function pointers.

## Verification

- `cargo check -p simple-runtime`: PASS
- checked float zero-versus-error test: PASS
- SFFI null/signature/performance guard: PASS
- Simple plugin wrapper check: PASS

No throughput percentage is claimed from this code-shape gate. The existing
LLVM/GPU performance suites remain the end-to-end benchmark owners and must be
run when their external libraries and hardware are available.
