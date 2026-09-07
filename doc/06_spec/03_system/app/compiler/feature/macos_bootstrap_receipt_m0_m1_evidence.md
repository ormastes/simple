# macOS Bootstrap Receipt M0/M1 Evidence

This evidence is host-independent and does not claim a native bootstrap or
native Intel qualification run.

| Cross-host row | Status | Evidence | Blocker |
|---|---|---|---|
| Apple Silicon macOS | **BLOCKED** | Portable/static receipt audit passes canonical framing, live-byte admission, provider/archive identity, and Darwin/ELF linker policy without claiming native qualification. | The isolated Stage3 worker terminated with exit code 1 and produced no candidate or provenance receipt. |
| Intel macOS | **BLOCKED** | The same host-independent contract applies to `x86_64-apple-darwin`. | No native Intel runner or retained Intel receipt is available. |

Authoritative review:
`build/review/m0_m1_mutation_focused_review_2026-09-02.md`. Stage3 recovery state is
recorded in `build/review/self_hosted_runtime_recovery.md`.

Performance authority is baseline-relative 10%. Each native row must first
publish an admitted architecture-matched baseline; missing baseline fails
closed. Maximum steady RSS is `<=110%` of baseline and maximum growth across
20 requests is `<=10%` of baseline RSS.

Production integration is owned by the `native-build` success funnel. The
driver publishes its admitted provider identity into the selected native cache;
the CLI derives the exact entry closure and Darwin target inputs, publishes the
canonical current-input receipt, and immediately reloads it through the
file-backed admission boundary before returning success. The focused
integration scenario invokes `cli_native_build` itself rather than calling the
receipt helper directly.

Native qualification also retains and digest-binds the executing runner's
`xcodebuild -version` and selected `cc --version` outputs. M5 revalidates both
their hashes and semantic version signatures through the immutable M4 evidence
manifest instead of trusting unbound workflow log text. The M4 and M5 receipts
also carry each slice's target-identity digest, canonical deployment target,
and SDK identity; any admission/M4/package drift fails closed.

Darwin admission fails closed when the backend provider receipt is absent. SDK
identity binds the exact `SDKSettings.json` or `SDKSettings.plist` digest while
keeping the SDK root out of the portable key. Admission rehashes those live SDK
settings and every recorded linker input instead of trusting a caller-supplied
digest. It also rehashes the exact resolved linker executable recorded by the
production linker wrapper. The linker consumes immutable cache snapshots and
records the complete ordered file list it actually passes
to `link_to_native`: user/module objects, the entry shim, runtime objects,
selected runtime archive from a `--runtime-path` directory, Stage4 projection,
bootstrap support object, and configured external providers. Each
recorded file must be Mach-O (or an archive whose payload members are Mach-O),
must contain the requested CPU slice, and has its exact digest bound into an
ordered manifest. Archive payload members carry ordinal, size, and digest
evidence. Every fat Mach-O table entry must identify a non-overlapping,
in-bounds thin Mach-O slice, and archives with truncated alignment padding are
rejected. Reordering two valid archive members changes the provider identity.
Paths remain receipt facts only; the content identity binds ordered
artifact bytes and architecture without making absolute worktree paths part of
the reusable action key. The target identity separately preserves the exact
backend provider receipt and that ordered content identity.

Focused commands, each attempted once:

- `scripts/check/check-macos-bootstrap-receipt.shs` — BLOCKED after the bounded correction cycle: the pure self-hosted deployed binary rejects `test`, `run`, and direct source entry. The checker accepts `SIMPLE_BIN` when a capable admitted self-hosted runtime is available.
- `scripts/check/check-macos-bootstrap-receipt.shs --portable` — **PASS** in the
  latest portable/static audit. This covers production wiring, output
  validation, SDK settings evidence, member/content binding, and negative
  production scenarios; it does not claim native execution.
- `scripts/check/check-macos-reverse-reference-m4.shs --self-test` — **PASS**;
  the exact eight-row contract and provider/archive mutation oracle reject
  synthetic or payload-preserving evidence.
- `scripts/check/check-macos-universal-m5.shs` — **PASS** for portable structural
  evidence. It rejects malformed retained Xcode/clang logs and target/SDK
  receipt drift while leaving native signing and cross-host rows **BLOCKED**.
- The focused SSpec remains available at `test/01_unit/app/build/macos_bootstrap_receipt_spec.spl`; the admitted binary does not implement the `test` command, so no SSpec PASS is claimed.
