# Canonical Stage 2 resume: backend composition admission failure

Status: canonical attempt failed; candidate rejected and preserved. No retry was
run after this attempt.

## Attempt

The reviewed cache-resume wrapper was invoked once with donor
`build/stage2-resume.WBRMDQ`. It created fresh output
`build/stage2-resume.DCrHkn`; the donor source manifests and copied cache were
byte-identical. The cache-resume contract passed before the run. At start,
18.5 GB was available and no competing bootstrap/build process was live.

Canonical command shape:

```text
SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/resume-stage2-from-cache.sh \
  /Users/ormastes/macos-stage4-codex-20260908/build/stage2-resume.WBRMDQ
```

Stage 2 linked an arm64 Mach-O compiler with `3 compiled, 880 cached, 0
failed`. The process then terminated with exit 2 during canonical sanity.

## Failure

Version and unsupported-command checks passed. The frontend smoke failed in the
hello-world positional build with status 1:

```text
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
```

This is distinct from the earlier backend-selector null dereference: there was
no SIGSEGV, no selector backtrace, and the failure is an explicit fail-closed
composition admission result.

## Evidence

- Rejected candidate: `build/stage2-resume.DCrHkn/stage2/aarch64-apple-darwin/simple.rejected`
- Candidate type/size: arm64 Mach-O, 139096760 bytes
- Candidate SHA-256: `1b6973e7a40a4722c7dcc9a2332b4fa5191e4465ec29e7a87b5e89cae781abdf`
- Sanity receipt: `build/stage2-resume.DCrHkn/stage3/aarch64-apple-darwin/stage2-sanity.env`
- Driver log SHA-256: `d13a2ac29c19549b6fb7972d5d41b12f56c277eef83ab5bf0aff5b7edc1ece12`
- Hello-world log SHA-256: `5a38eb31bbdba2be6144c86a0598c97aec2af006df4297deb0d0338aeabfc6bd`
- Full wrapper log: `build/mini_builds/stage2-canonical-after-backend-fix.log`
- Canonical transcript: `build/stage2-resume.DCrHkn/stage3/aarch64-apple-darwin/stage2-command.transcript`

The candidate was not admitted and must not produce the Chrome oracle library.
The next investigation may use the retained candidate under a diagnostic
backtrace, but another full Stage 2 retry is outside this attempt.

## Subsequent cache-preserving validation (2026-09-09)

Per the retry boundary, one additional canonical validation was run after the
`module_surfaces` diagnostic dereference was replaced with a nil-coalescing
projection. The reviewed resume wrapper accepted donor
`build/stage2-resume.DCrHkn`, cloned its completed native cache, and delegated
to the canonical bootstrap once. No competing bootstrap process was live at
start; the filesystem had 16.7 GiB free. The resume contract passed.

Stage 2 linked successfully (`3 compiled, 880 cached, 0 failed`), but the
canonical frontend sanity gate rejected the candidate during the hello-world
positional probe with the distinct fail-closed error:

```text
PLUG-E-K1-POLICY: bootstrap backend composition admission failed
```

Current retained evidence:

- Rejected candidate: `build/stage2-resume.MbhTTc/stage2/aarch64-apple-darwin/simple.rejected`
- Candidate: arm64 Mach-O; SHA-256 `0573f188f532ad04cc1fa09c606beadac492f518e386d23d31076855561bc720`
- Sanity receipt: `build/stage2-resume.MbhTTc/stage3/aarch64-apple-darwin/stage2-sanity.env`
- Frontend status: `build/stage2-resume.MbhTTc/stage3/aarch64-apple-darwin/stage2-sanity.env.frontend-bootstrap-0.status.env`
- Driver/failure log SHA-256: `d13a2ac29c19549b6fb7972d5d41b12f56c277eef83ab5bf0aff5b7edc1ece12`
- Hello-world log SHA-256: `5a38eb31bbdba2be6144c86a0598c97aec2af006df4297deb0d0338aeabfc6bd`
- Canonical transcript: `build/stage2-resume.MbhTTc/stage3/aarch64-apple-darwin/stage2-command.transcript`

No Stage 2 admission receipt was published, and the rejected candidate was
not used to build the Chrome oracle. No further full-build retry was run.

## Astra diagnosis: native text ordering compares addresses (2026-09-09)

Status: exact rejected condition identified; pure-Simple registry repair and
focused native ordering verification complete. Whole-registry execution and
canonical Stage 2 admission remain unverified. No Stage 2 retry was run during
this investigation.

The failure is in `static_backend_registry.spl::_table_is_sorted_v1`, before
the policy-specific length, kind, and link-class checks. Its source expression
`name <= previous` was compiled as an integer comparison of tagged text
addresses. This is the existing compiler defect tracked in
[native_string_relational_operators_compare_raw_handles_2026-07-17.md](native_string_relational_operators_compare_raw_handles_2026-07-17.md),
not a request for looser composition admission.

The retained `MbhTTc` candidate still has SHA-256
`0573f188f532ad04cc1fa09c606beadac492f518e386d23d31076855561bc720`.
Bounded LLDB inspection, with inherited environment disabled, reproduced the
same status 1 and diagnostic. Read-only breakpoint instrumentation recorded:

| Index | Current name/address | Previous name/address | Raw address `<=` |
|---|---|---|---|
| 0 | `cranelift`, `0xc20c72821` | empty, `0x108e19ac1` | false |
| 1 | `interpreter`, `0xc20c72911` | `cranelift`, `0xc20c72821` | false |
| 2 | `llvm`, `0xc20c6fc61` | `interpreter`, `0xc20c72911` | true |

The strings were read from their runtime headers and UTF-8 bytes; they are
valid and correctly ordered by content. At
`_table_is_sorted_v1 +152`, `ccmp x21, x24, #0x4, eq` compares the addresses.
The next instruction, `b.le` at `+156`, reaches the false return at `+220`.
The function returns tagged false `x0=0x13` to
`validate_k1_static_backend_table_v1`; the process then emits the recorded K1
error and exits 1. No debugger register writes or bypassed branches were used.

### Harness comparison

| Input | Canonical probe | Diagnostic reproduction |
|---|---|---|
| Candidate | Stage 2 filename before rejection | Same bytes at retained `.rejected` path |
| Arguments | Positional hello-world source, LLVM, `core-c-bootstrap`, entry closure, one-binary | Same flags and source; private diagnostic cache/output paths |
| Working directory | Pinned smoke starts in evidence directory; bounded child explicitly changes to repository | Repository directory |
| Environment | Scrubbed, isolated HOME/TMPDIR, locale C; candidate/delegate identity, bootstrap 0, cold package-index initialization, no stub fallback | Inheritance disabled; same isolated HOME/TMPDIR and relevant Simple variables; bounded tool PATH |
| Descriptors/output | Held evidence FDs 6/7/8, pinned collector, stdout/stderr pipe | LLDB launch and debugger capture; no canonical evidence descriptors |

The pinned shell/collector restore the compiler's repository working
directory correctly. The selected composition is the committed
`kernel_llvm_cranelift` implementation: its table has the three expected
entries. It reaches the real validator, not the fail-closed unselected module.
No environment-based policy override is involved in that function. Allocation
addresses explain why an earlier manual reproduction could advance beyond K1;
the exact allocation difference induced by each launch configuration was not
individually bisected and is unnecessary to fix content ordering. The
diagnostic run is not a substitute admission receipt.

### Repair and verification

`static_backend_registry.spl` now uses the private
`_backend_name_precedes_v1(previous, name)` helper in both sorted-table
validation and `select_static_backend_v1`. It compares character codes and
then prefix lengths. Empty-name rejection, strict ordering, duplicate
rejection, kind/name matching, exact K1 membership/link classes, policy identity,
and ABI negotiation remain in place. The general native relational-operator
compiler defect remains open in its existing bug record.

Evidence directory: `build/native_probe/astra-k1-policy.XknXh9/`.

- `k1-trace-confirmed.log`: exact rejecting branch and exit; SHA-256
  `2af8cb447354aad15792361c221823690358d22d5ef4d695d1132bd81aa2f25a`.
- `registry-fixed-disassembly.log`: actual repaired registry object calls
  `rt_string_char_code_at` and compares character values. Both validation and
  selection call the new helper (relocations at `0x428` and `0xf0c`).
  Disassembly SHA-256:
  `bc8f2dccc23b207aecc170a707e2b2261744b5f0786a9a2cc6b0bc37d2c0787e`.
  The object is `native-cache/scope-12dcff39146f2980/objects/dc8d01e79c9540f8.o`,
  SHA-256 `f94b08686a27fb5d9d061758d53db41535b6e2bd34c059e197bb0a5ac681390a`.
- `content-order-projection.spl`: diagnostic copy of the exact private helper,
  checked byte-identical against production before compilation. The native
  ARM64 executable passed all 49 ordered pairs of seven names, including
  empty strings, separate equal-content allocations, prefixes, and reversed
  order. See `comparator-build.log` and `comparator-run.log`. This is helper
  evidence only, not complete registry or compiler admission.
- `test/fixture/native_backend_registry/policy_content_order.spl`: permanent
  real-registry regression with 22 checks for the accepted policy, all invalid
  permutations, unknown policy, missing/duplicate entries, wrong link class,
  prefix ordering, empty/mismatched descriptor names, and installation.
  Its one build attempt failed in the existing unrelated
  `src/compiler/60.mir_opt/mir_opt/mod.spl` dependency on unresolved
  `Result.err`. `policy-build.log` preserves that failure. It did not link or
  execute; those 22 checks are **not PASS evidence**.
- The focused native artifacts were produced using the retained Rust bootstrap
  authority with `SIMPLE_NO_STUB_FALLBACK=1`, solely for bootstrap diagnosis.
  No candidate was admitted, no receipt was fabricated, and no Chrome library
  was built from a rejected compiler.

One future canonical cache-preserving retry is justified by the measured
root cause and changed registry machine code. It must still pass both frontend
bootstrap modes, actual positional hello-world link/run, and all normal
admission/provenance checks before producing the Chrome library. This report
does not authorize bypassing an exhausted session retry cap.
