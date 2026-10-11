# Fixed compiler worker payload routing

Executable: `test/01_unit/app/cli/native_build_worker_routing_spec.spl`.
Status: authored manual; execution UNRUN. This is not generated PASS evidence.

The compiled full CLI recognizes only inherited, marked requests to its two
fixed compiler-worker entrypoints. Source admission, backend selection and policy
handoff validation remain required. Payload extraction precedes generic CLI
filtering so worker flags retain their meaning.

| Scenario | Action | Required result |
|---|---|---|
| Ordinary run | Omit the worker marker | No worker admission or payload |
| Unknown entry | Mark a user script as a worker | No worker admission or payload |
| Native payload | Pass backend, progress and opaque handoff arguments | Exact argument order and bytes retained; native route selected |
| Parse payload | Pass an absolute fixed parse entry and shard/source/entry flags | Parse route selected; exact payload retained |
| Empty payload | Mark an allowlisted entry without arguments | Admission true, empty payload; handoff validator must subsequently reject it |
| Truncated argv | Omit command or entry | Admission false without out-of-bounds access |
| Wrong verb | Use test with a worker filename | No worker admission or payload |

The helper scenarios do not establish end-to-end compiled dispatch, bootstrap
resource behavior or Phase3 admission. These require rebuilt executable evidence.

The standalone 16-check native probe reached LLVM code generation for both
modules on 2026-10-11, but linking failed before an executable was produced.
The producer requested the absent legacy `runtime_raw_u32.c` in the working
checkout despite the frozen runtime override. Its log also reports a rejected
array handle and possible compiler/FFI ABI mismatch. Neither the probe nor these
seven SSpec scenarios has run; this diagnostic is FAIL, not assertion evidence.

Follow-up native evidence (2026-10-11): the byte-identical standalone probe
compiled and ran after correcting the C-runtime source root and materializing
the pinned SDK header. It printed `PASS: native worker routing checks=16` and
exited 0. Both receipts are quiescent with the 5 GiB cap enforced. The imported
routing helper blob is unchanged across the rebase. These are executed helper
checks; the seven SSpec scenarios and end-to-end full-CLI dispatch remain UNRUN.
Phase3 admission remains blocked by the subsequent compiler build failure.
