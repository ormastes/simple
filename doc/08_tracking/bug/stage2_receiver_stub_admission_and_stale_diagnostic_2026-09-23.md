# Stage2 receiver admission admitted stubs and attributed a stale failure

Status: shell contracts fixed; native Stage2 admission remains unverified.

## Reproduction

Bootstrap source `7f4e04d70627a0fee1258a8f751aad5aca9d6959`, macOS arm64,
reached a successful five-check frontend sanity gate. Its subsequent receiver
probe printed the expected output and `bootstrap_stage2_struct_receiver=PASS`
after reporting `Generating 7 stub functions for unresolved symbols...`.
The first receiver build cleared `SIMPLE_NO_STUB_FALLBACK` on every target
except Windows MSVC, overriding strict settings inherited from bootstrap.

The positional Stage3-route probe subsequently failed with raw status 132.
The diagnostic selector instead displayed a previous run's frontend failure.
The current hashed frontend receipts both passed. The sanity preflight archived
the normal driver/probe logs but omitted `.frontend-failure.log`.

Original evidence is retained in the P0 worktree under
`build/evidence/macos-enforced-bd544/stage2-backend-receiver-7f4e04d/`.
The compiler SIGILL and missing runtime symbols are separate compiler/runtime
issues; this shell change does not resolve or qualify them.

## Correction

Both receiver admission builds now require `SIMPLE_NO_STUB_FALLBACK=1` on all
targets. Existing Windows ABI and linker-flavor selection remain intact.
The existing sanity preflight archives `.frontend-failure.log` together with
the other prior evidence before the new run. Its diagnostic selector therefore
sees current logs, while the prior failure remains recoverable in the archive.

## Focused verification

`sh scripts/check/check-stage2-admission-helper-contract.shs` executes the
shipped receiver helper with synthetic compilers across Darwin, Linux, Windows
MSVC and Windows GNU targets. It checks both clean admission probes, explicit
strict settings despite an ambient value of zero, exact platform ABI settings,
rejection of unresolved symbols before any PASS marker or subsequent probe,
and archival plus current-only attribution using the real diagnostic selector.

Before the production fix: 16 assertion failures. After the fix: 55 checks,
zero failures. This is shell-contract evidence, not native compiler evidence.
On the macOS host, `/usr/bin/time -l` recorded 2.10 seconds wall time and
2,490,368 bytes maximum process RSS for the test suite. Receipts are in this
worktree's `build/evidence/stage2-admission-helper/` directory. No native build,
bootstrap, or push was run for this check. The production change introduces no
new process or loop: it changes one environment value and adds one file to the
existing constant-sized archival list. No native performance claim is made.
