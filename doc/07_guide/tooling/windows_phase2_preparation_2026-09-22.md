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

## Alignment with the later Stage2 candidate

After the initial preparation at `99400f03fa17c7681196761587343e217bbcaee5`,
the following independently reviewed fixes from the frozen bootstrap lane were
applied to this repository's local `main`, without conflicts:

| Bootstrap-lane commit | Prepared-lane commit | Fix |
| --- | --- | --- |
| `8138fe3b2ac1410c82fbcfc855443f6c8d97c33f` | `b0dbeab1d536f1e13ba069e6a6113b1aff16509b` | Pinned gitlinks |
| `76f69029547056c0c41339edae4255c80e51e58e` | `67d3506b314eed0a41aadbf4eeaa76871b96ca1b` | Literal bracket paths |
| `418418aa13469faac3701bfe9040a0914d70b2d3` | `53222a70426ebfbcce04f3a8a04e522767a5280c` | Bounded current-tree inventory capacity |
| `e791654e36a282fd614350035d63cb83a14c80cf` | `56bb573075c14c8c16a4f0337337d090f2eaa8a5` | Bound MSYS gitlink root spelling |
| `e232e7657beac1d56611bb32cf3017861da988ae` | `f66110d6cff1d7c39bf50f7bbcfd468a60be1041` | Owner-bound generated native symlink |
| `392a899c0b7269637ca70c46f239d623b3078799` | `76125ad93ec56d4d7091cd4079fd9c3df6e34ecc` | Frontend Job cleanup after root exit |

Git-tree comparison against `392a899c0b7269637ca70c46f239d623b3078799`
shows exact identity for all nine files touched by these six imports, including
the complete authority helper, native collector, frontend admission helper,
and their regressions. The only remaining differences from that candidate are
the previously prepared Phase2 scripts, tests, and documentation. No Phase2
implementation files were modified by the six imports. The tracked count grew
from 137451 to 137455, matching four added files.

Existing focused evidence for the identical imported code is reused; none of
the passing suites was rerun. This is source-alignment evidence, not a new
Stage2 admission or a claim that the Phase2 binary matrix has passed.

Before execution, review the actual admission for the `392a899` candidate,
its compiler SHA, runtime snapshot and current source snapshot. The prepared
verifier locates helper programs beneath `--source-root`, so merely invoking
this verifier with the untouched bootstrap checkout as source root does not
supply the new capsule-binding helpers. A full, prepared source checkout or
explicitly reviewed integration is required; this sparse repository alone is
not a production execution root. Never relabel a rejected compiler or rewrite
old receipts to claim the new helper/Git identity. The main agent owns that
integration and all subsequent execution scheduling.

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

The initial sparse checkout omitted the complete source inventory and could
not resolve a production admission. The main agent subsequently authorized a
full LFS-smudge-disabled checkout, initialization of the recorded SPipe gitlink,
and current-HEAD materialization in this isolated repository. Available D:
space before expansion was 69,522,481,152 bytes, above the 10 GiB build floor.
The resulting receipt and canonical source snapshot are to be retained under
`build/mini_builds/phase2-prepared-source/`, after committing this report so
the materializer sees a fixed HEAD. Completion is established by those runtime
evidence files, not this prospective description. No Phase2 build is authorized
until the main agent reviews the real Stage2 admission and snapshot comparison.

## Supported external admitted-compiler route

Contract inspection confirms that a full prepared source checkout may consume
the admitted `392a899` compiler at its original external path. The Phase2
binding contract does not require the same repository HEAD, Git-state hash, or
helper hash. It requires exact admission-v2 candidate path/hash, stable
admission bytes, the admission-bound runtime snapshot, and a recomputed canonical
compiler-source snapshot equal to `source_snapshot_sha256` in that admission.
The snapshot format uses paths relative to the source root, but includes link
text and resolved relative targets. Equal committed source trees are therefore
necessary evidence, not sufficient proof of equal materialized snapshots.

The source roots and `command-snapshot.shs` are byte-identical in the prepared
tree and `392a899`. The explicit resolve operation must still prove their
actual on-disk equality. No contract override or receipt rewriting is needed
or permitted. The compiler cannot simply be relocated: its admission's
`candidate_path` is checked exactly.

After the real admission exists and the full prepared checkout is ready, the
main agent can use this supported sequence (not executed during preparation):

```sh
set -eu
phase2_root=/d/b-phase2
phase2_admission=/d/b-sync/build/bootstrap-sync-20260922/stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env
phase2_field() {
    awk -F= -v key="$1" '$1 == key { count++; value=substr($0,index($0,"=")+1) }
        END { if (count != 1) exit 2; print value }' "$2"
}
phase2_compiler=$(phase2_field candidate_path "$phase2_admission")
phase2_compiler_sha=$(phase2_field candidate_sha256 "$phase2_admission")
phase2_runtime=$(phase2_field runtime_authority_path "$phase2_admission")
phase2_work="$phase2_root/build/mini_builds/phase2-real-$phase2_compiler_sha"
phase2_capsule=$(sh "$phase2_root/scripts/bootstrap/phase2-runtime-binding.shs" publish \
    "$phase2_compiler" "$phase2_runtime" "$phase2_root/build/phase2-runtime-capsules")
sh "$phase2_root/scripts/bootstrap/phase2-runtime-binding.shs" resolve \
    "$phase2_compiler" "$phase2_root" "$phase2_work"
SIMPLE_NO_STUB_FALLBACK=1 sh "$phase2_root/scripts/bootstrap/bootstrap-phase-verification.shs" \
    --phase=stage2 --compiler="$phase2_compiler" --compiler-sha256="$phase2_compiler_sha" \
    --strategy=full --hash-policy=canonical --source-root="$phase2_root" \
    --runtime-path="$phase2_capsule" --work-root="$phase2_work" \
    --cache-root="$phase2_root/build/bootstrap/tool_cache"
```

`publish` adds a new capsule binding sidecar beside the original compiler;
it does not rewrite `admission.env`. Existing differing bindings are rejected.
Permission failure or any source/runtime mismatch is a blocker to investigate,
not permission to thaw or forge existing authority.

The Stage3 planner-admission-v2 key set binds parent compiler, Stage2 sanity
and provenance, runtime snapshot, Git state, planner source/closure, and planner
execution. It contains no Phase2 verification summary/test-receipt field, and
Stage3 resume does not consume one. Thus a planner bootstrap receipt does not
itself prove this Phase2 gate. Retain the Phase2 summary, command-owner receipts,
executed-count inventories and logs separately; the main agent must require
their PASS before scheduling Stage3 as the restart plan directs.

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
