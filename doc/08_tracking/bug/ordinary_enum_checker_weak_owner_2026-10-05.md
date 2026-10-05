# Ordinary C runtime enum checker ownership

Status: focused Linux ELF native mixed-link regression PASS and actual Phase2 ordinary-runtime optional-enum application regression PASS. Windows/MSVC, other object formats and broader compiler matrices are not qualified here.

The ordinary bundle includes runtime.c and runtime_native.c under allow-multiple-definition. Legacy enum construction/getters were weak while two legacy checkers were strong. Consequently a legacy-first link selected tagged registered-heap constructors but raw-pointer checkers. Actual afaa Phase2 optional fixture built successfully and failed native matching; a separate diagnostic failed all five enum cases, including ordinary integer payload. Evidence: WSL build/item5-optional-nil-diagnostic/diagnosis.md and original build/item5-owner-nil-tests/optional/probe. Matching constructor/callsite enum IDs excluded optional-nil lowering as this runtime cause.

The four-line repair marks legacy rt_enum_check_discriminant and rt_enum_check_variant SPL_WEAK, consistent with the four neighboring legacy enum operations. Native registered-object checks remain the authoritative strong definitions. Standalone legacy bodies and their i32 comparison semantics are unchanged. No unchecked representation copy or forwarding/sentinel change is introduced. SPL_WEAK is empty for MSVC proper; this patch does not establish MSVC mixed-owner resolution.

## Actual native results

Source base4bba42dd0ddbd88129219edfffe8de6aeb1c1895. Clang23 Linux compile, O2, section GC, ordinary allow-multiple-definition link. C test calls real rt_enum_new/getters and both checker APIs. It covers typed/wrong-owner/wrong-discriminant variants, zero stored/expected ID compatibility, payload preservation, nulls, native invalid immediates/non-enum registered objects, and wide expected IDs/discriminants. Standalone legacy mode tests existing i32-cast behavior and does not pretend arbitrary invalid raw pointers are supported.

- legacy-first mixed link: PASS30 checks; binary530cc3cb1c5499ed1cab15642eddca70c81aac2805f2dd01883a3a0474648e3e.
- native-first mixed link: PASS30 checks; binary091c72a06de5d018ecc46319a273d3c193444933fbb442d5d55a4c2febf81f57.
- standalone legacy link: PASS16 checks; binary05526a4fd28f6d65deb4a0db824357c8833541572c285d7097bc19dab4a2ab68.

Retained output `/var/tmp/item5-enum-runtime-owner-20261005/` includes compile/link/run logs, objects, artifacts.sha256 and enum-symbols.txt. nm shows W for all six runtime.o enum operations and T for the native definitions of ctor/id/discriminant/payload/check_discriminant/check_variant. Production runtime.c source SHA256 c6fd730ad4b35756a0eb7ead893eb0c145534eb21b64a7e2ec8679ad4ed5e1d6; test source123033c4e4626d2be699a0d037af134e7add061a073daeb20346f67aff55786f.

The exact executed setup scripts remain at build/review/run-enum-owner.sh and finish-enum-owner.sh in the isolated worktree. Initial setup failures are retained: runtime_memory compilation needed _GNU_SOURCE for pthread_rwlock declarations; standalone link initially encountered existing spl_f64_to_bits duplicate and then used ordinary allow-multiple-definition. The already-green two mixed executables were not rerun. These setup failures are not represented as compiler defect reproductions.

Reproducible checked-in checker: `CC=/usr/lib/llvm-23/bin/clang NM=/usr/lib/llvm-23/bin/llvm-nm bash src/runtime/test/check_enum_mixed_owner.sh /var/tmp/enum-owner-new-attempt`. Each compilation/link/run has a finite timeout. It compiles the same production owners with the successful per-TU flags, links both orders and legacy-only, executes actual outputs and retains hashes/symbol census. The consolidated wrapper was syntax checked; its component commands produced the actual results above. No redundant native matrix rerun is claimed.

This is runtime ownership evidence, not a full native compiler, vector, DB or live HTTP PASS. The separate positional CLI runtime selection defect remains separately owned.
## Actual Phase2 application boundary closed

Parent retained the same afaa53e061807d11b0e36b79088c3af3a4e51c5dc3d224f6b5683f181af49f4c compiler and unchanged three-case optional fixture, applied only this runtime.c ownership repair to its C source authority, explicitly unset SIMPLE_NATIVE_RUNTIME_BUNDLE and SIMPLE_RUNTIME_PATH and omitted runtime flags. This validates the previously failing ordinary runtime, not a core-C substitution. Build exit0, native run exit0, `checks=3 failures=0`.

Evidence directory `/var/tmp/simple-item5-phase2-20261005/build/item5-enum-owner-ordinary-runtime/optional/` contains logs, source/binary hashes, status and both watchdog receipts. Native binary SHA256 `7d51ad58b17222064fc1d901ab2f08a8d48d6c0b8497de2d39f6e5ecb1b8d9b1`. Build peak552088 KiB, run peak8128 KiB; both exit0 and quiescent1. Root's source checkout is4bba plus separately reviewed compiler overlays, but the executed compiler remained the same immutable afaa artifact; no new compiler qualification is inferred from this C-owner repair.

Static validation: direct-env working/staged PASS, spec layout0, checker bash syntax PASS and diff-check PASS. Canonical mandatory local tier passed14/0failed on implementation commit468515f332209af787182e3c2932caa5b16bd941, explicit release base4bba; logs/results build/review/enum-owner-local.*. The subsequent documentation-only update records the newly completed Phase2 result; no green native checks were repeated.
