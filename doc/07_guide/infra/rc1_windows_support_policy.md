# RC1 Windows support policy

RC1 requires one fully qualified host: `x86_64-pc-windows-msvc`. The selected
runner is the local Windows host (`self-hosted`), using the admitted LLVM/MSVC
toolchain. One successful host means its complete required bootstrap and tests
pass; it does not mean one backend, one phase, or one smoke test is sufficient.

The authority is [release/support.sdn](../../../release/support.sdn). Its `rc`
section has exactly one required target. Alpha, beta and stable retain their
existing Linux requirements. The policy is keyed by channel, not prerelease
number: it applies to RC candidates until deliberately changed. RC2 must freeze
its own intended support matrix before qualification; additional host success
cannot be inferred from Windows success.

`availability: supported` is an allowed policy category, not observed evidence.
The parser permits `supported`, `blocked`, and `experimental`; it requires a
required target to be supported and nonexperimental. For a Windows receipt the
existing matrix renderer reports optional Linux x86 as `not_executed` and
Linux AArch64 as `experimental`. Both remain unverified for RC1. Undeclared
platforms are also unverified. No other-host PASS or package should be invented.

Every declared row still requires `bootstrap: full` and `whole_tests: required`.
The actual Windows qualification must preserve the complete bootstrap lineage,
both backend test requirements, all required products, and the whole interpreter
suite. Early Phase4 built from Phase2 is diagnostic evidence; it does not replace
the required Phase3-to-Phase4 lineage. Diagnostic checker exceptions must be
removed for formal qualification. Failed, missing, skipped or resource-aborted
required checks are not PASS.

## Policy check and evidence boundary

Using the qualified self-hosted release runtime, the existing policy query is:

```text
simple release support-check --root=. --channel=rc --observed-target=x86_64-pc-windows-msvc --json
```

This checks the declared target coverage and renders a matrix. It does not run
bootstrap/tests, authenticate artifacts, or prove the supplied observed target.
Its JSON `passed` labels are suitable only after an evidence owner has verified
the real target's complete receipts. A Linux observed target is rejected for RC.

Candidate identity binds source, version, policy, toolchain, support manifest,
build graph and evidence hashes. Changing this policy changes that identity;
old candidate receipts cannot be relabeled. Existing `candidate-admit` records
admission metadata, and `promote-check` produces a promotion authority plan.
Neither substitutes for verifying the receipt files and immutable artifact bytes.

## Remaining Windows admission and publication integration

At this change's base, `.github/workflows/candidate.yml` uses `ubuntu-latest`,
Linux tool installation, Linux runtime discovery, a Linux observed target,
Linux package/deploy paths and Linux attestation subjects. It cannot produce a
Windows RC1 qualification by changing the support row alone. The older
`.github/workflows/release.yml` builds platform packages; it is not an importer
for the current local immutable candidate admission. `publish.yml` publishes npm
packages and likewise is not that importer.

The separately owned local Windows admission path must:

1. Read actual immutable Windows bootstrap, full-test and deployment receipts;
   reject missing, failed, mismatched or diagnostic-only evidence.
2. Bind the exact Windows PE, required DLLs/products, source/producer/runtime,
   support policy and toolchain identities. Validate package members and hashes.
3. Feed verified evidence into the existing qualification and candidate-admission
   contracts, preserving create-once candidate identity and review authority.
4. Promote those same verified bytes without recompilation when tag/publication
   is subsequently authorized. Record other hosts as unverified.

This policy change performs no deploy, tag, upload or publication. Local Windows
bootstrap is still in progress. The four added Simple policy regressions are
authored but native execution is pending; source/data checks are not full RC
qualification.
