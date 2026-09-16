# Push no-direct-rt stale baseline blocked zero-delta branches

## Symptom

`push-no-direct-rt` rejected a SciLib topic with 6,313 forbidden sites even
though `origin/main` contained the same 6,313 sites. The older tracked baseline
was 6,072, so unrelated mainline debt made every otherwise clean topic fail.

## Root cause

After the gate moved to committed-ref mode, push admission still compared the
tip with the historical tracked baseline rather than the outgoing range base.
That answers whether the whole repository meets an old snapshot, not whether
the proposed branch introduces debt.

## Fix and evidence

`check-no-direct-rt.shs` now accepts fail-closed `--baseline-rev` with `--rev`.
It measures both committed trees with identical roots and allowlist semantics.
The push dispatcher supplies the outgoing range base; standalone and critical
lanes retain their prior semantics.

- Selftest: 19/19, including unchanged-debt PASS and added-debt FAIL fixtures.
- SciLib topic: tip 6,313; `origin/main` 6,313; PASS.
