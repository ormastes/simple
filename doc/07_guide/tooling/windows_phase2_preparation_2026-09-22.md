# Windows Phase 2 preparation, 2026-09-22

## Scope and integration

Prepared in independent repository `D:/b-phase2`, local `main`, based on
`cfb58af2b0afc2aeafa4e58a7f7be5ed2aa5cde6` from `D:/b-sync`.
Shared Git objects are read-only inputs; refs, index, sparse checkout, test
outputs, and writable caches are independent. The running bootstrap checkout
was not modified. No bootstrap, native build, deployment, or push was started.

| Selected source commit | Integrated commit | Purpose |
| --- | --- | --- |
| `9988fb7ccd99ec84875950eced8ad80e68868cb2` | `7755e219a1d` | Reject vacuous compiler inventory JSON |
| `d75c2ba09d7fabd242aea895460a7ad04cea5811` | `b785aed08a7` | Preserve fixture JSON escapes |
| `491ab5a6fed1751a44f4f0d9d2a5023d61a68ea9` | `a1662d7c5e1` | Executed-count gates and command ownership |
| `9be71b1de38146ee478729f164ba7cade01ee83b` | `be6de6717fc` | Portable loader behavior oracle |
| `17685643072a1d18b5483db96bc328dc7d1c329c` | `007f9036edb` | Correct Windows RSS accounting introduced by previous commit |
| `ff2b2edb47ba19321b8a96e3a668d4e5865743af` | `613e343e02f` | Admission-bound Windows v2 runtime capsules |
| `3625d51e9d673dfade7aed4e2d7e1ed825ae2e34` | `d570c401205` | Match producer and consumer artifact layouts |

All seven commits applied without conflicts. The tracked count increased from
137441 to 137450, corresponding to nine added files. No Rust compiler, vendor,
LLVM detector, or setup toolchain files changed; LLVM18 seed binding remains.
The separate native C frontend prerequisite remains LLVM23 clang-cl in C mode.

The additional repair extracts only the compiler-inventory `find`/`sort`
failure handling and its regression from
`71c0002764af2069e6f4bd205dd43895a6b41e11`. It does not import that commit's
LLVM23 detector changes. Partial discovery and failed sorting must fail closed.

## Focused evidence

Tests ran once each under `C:/msys64/usr/bin/bash.exe`, with
`SIMPLE_NO_STUB_FALLBACK=1`. Logs are retained in
`D:/b-phase2/build/mini_builds/phase2-focused/`.

| Program | Result | Log |
| --- | --- | --- |
| `bootstrap_compiler_unit_execution_count_test.shs` | PASS | `bootstrap_compiler_unit_execution_count.log` |
| `bootstrap_phase2_portable_loader_contract_test.shs` | PASS | `bootstrap_phase2_portable_loader_contract.log` |
| `bootstrap_windows_rss_contract_test.shs` | PASS | `bootstrap_windows_rss_contract.log` |
| `phase2_runtime_capsule_contract_test.shs` | PASS | `capsule-contract.log` |
| `bootstrap_phase2_capsule_consumer_compat_test.shs` | PASS | `capsule-consumer.log` |
| `bootstrap_phase_command_owner_test.shs` | PASS | `command-owner.log` |

All six focused programs passed with exit zero on their first invocation; no
scenario-count total is claimed because
these programs emit terminal verdicts rather than a uniform scenario counter.
The extra command-owner program uses synthetic tools and mutation matrices;
its terminal PASS was collected at 20:08:05 KST after approximately 17 minutes
28 seconds (launch observed at 19:50:37). It covered missing/false JSON,
command-owner and receipt mutations, runtime replacement, and producer
snapshot mutation. The long duration includes repeated full synthetic
matrices and MSYS process overhead; it is not a native build measurement.
Shell syntax, Perl validator syntax, and whitespace checks passed. No green
program was rerun. The tracked `doc/06_spec/*_spec.spl` count was zero.

## Admission and source binding

`phase2-runtime-binding.shs publish` checks compiler/admission hashes and binds
runtime leaves to the admission-hashed runtime snapshot before publishing a
capsule. `resolve` verifies that binding and recomputes the canonical source
snapshot. It rejects stale source, altered admission, and changed runtime.

The source snapshot currently covers `src/compiler`, `src/app`, `src/lib`,
`src/compositions`, and `examples/10_tooling`
(`scripts/check/lib/bootstrap-stage3/command-snapshot.shs`,
`bootstrap_stage3_source_snapshot_once`). These preparations change only
scripts, tests, and documentation, so they do not themselves alter that source
snapshot. This does not establish reuse of full bootstrap authority: Git,
bootstrap script, helper bundle, command transcript, and planner bindings are
separate identities and must still match their consumers.

This sparse checkout intentionally omits the complete source inventory and
cannot resolve a production admission against current source. Do not invoke
the downstream matrix here or adopt these scripts into the running candidate.
The main agent must first review actual Stage2 admission and all relevant
source/helper/Git bindings against the full materialized checkout.

## Downstream gate, not executed

After a valid current admission and capsule exist, the supported entrypoint is
`scripts/bootstrap/bootstrap-phase-verification.shs` with `--phase=stage2`,
the admitted compiler and receipt-bound SHA, `--strategy=full`,
`--hash-policy=canonical`, full `--source-root`, and private `--work-root` and
`--cache-root`.

The verifier builds distinct full CLI and test-runner entry closures. Cache
identity includes phase, producing compiler SHA, runtime identity, and
`full-cli` versus `test-runner`. Executable test rows require strict terminal
JSON with nonzero executed counts; no output-free exit zero is admission.
Bootstrap and portable loader suites run in interpreter and compile modes;
compiler specs receive per-file terminal results. These focused shell fixtures
are not evidence that those real binary suites have executed.

Only after the real Phase2 gate passes may the main agent schedule Stage3 via
`bootstrap-from-scratch.sh --resume-stage3-from-admitted=OUTPUT
--bootstrap-receipt=PLANNER_RECEIPT`, with valid planner-admission-v2 targeting
`//bootstrap:stage3`. Stage3 provenance and acceptance remain unverified here.
