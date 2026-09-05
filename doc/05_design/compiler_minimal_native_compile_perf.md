# Minimal Native-Compile Performance Detail Design

## Data

- `MinimalCompileCampaignRequest` carries compiler/receipt/fixture/work paths,
  timeout, fixed run count, and admitted baseline values.
- `MinimalCompileDecision` carries an explicit boolean and stable reason.
- `MinimalCompileCampaignResult` carries status, first failure reason, sample
  count, p50/p95 microseconds, max RSS KiB, and the final artifact SHA-256.

## Algorithms

Admission compares the observed compiler hash with both the requested hash and
receipt, requires exact receipt lines, and rejects seed-marked version text.
Each sample invokes `/usr/bin/time` directly (no shell), disables incremental
compiler caching, then validates and executes the output. Insertion sort over
five values selects indices 2 and 4 as p50 and conservative nearest-rank p95.
Integer cross-multiplication applies the 120% time and 110% RSS gates.

## Errors

Environmental prerequisites return `blocked`; a started campaign with a bad
compile, artifact, measurement, or budget returns `fail`; only all five valid
samples within budget return `pass`.

## Verification design

The SSpec checks three admission paths, three artifact paths, three budget
paths, and one live campaign. The live case has no skip branch: absent qualified
inputs makes its real `status == pass` assertion fail.
