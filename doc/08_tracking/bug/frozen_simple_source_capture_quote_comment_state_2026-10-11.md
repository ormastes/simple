# Frozen Simple source capture hides imports after apostrophes in comments

Status: repaired in private attempt2; compiled loader qualification remains blocked by HIR. Bug DB reconciliation pending.
Affected owner: build/native_probe/pure-loader-api-20261011-astra/prepare_source.py.
Execution ledger: compiled Pure loader API criterion, attempt1 of at most3.

## Actual evidence

The admitted Pure producer a6b18fd84c5f88a48afa0beaf61434f39678155fb0f0ed01127db25a28cf5078
ran both isolated positional native-build commands. Both exited1 in source
loading after72files; neither fixture executable was built or run. Compiler
PIDs55580/50988 were recorded, final owned Job counts0, all5738 input pins
unchanged. Compile wall times2.817/2.840seconds, peak sampled36608/36512KiB.
RESULT SHA2349badea4827b62048386a70ba1ab7beed2d99f32b13548d4eb30a3f345171a.

Both authenticated logs list unresolved compiler.core.frontend,
compiler.common.gc_config, compiler.core.interpreter.interp_resource_tracker,
std.common.crypto.sha256 and std.nogc_sync_mut.io.pipe. These failures are capture
omissions, not demonstrated loader source or runtime API failures.

The one-off capturer masks quote literals before handling comments. Apostrophes
inside comments therefore consume subsequent code as strings. Astra compared
frozen123SPL inputs and found23 hidden directives across4files, including all5
reported imports. Zero unresolved lexical probes was too weak to admit complete
capture; the actual producer correctly rejected incomplete source resolution.

## Repair and prevention

Use one stateful scanner that distinguishes code, line comments, strings,
escapes and multiline strings. Recognize comment markers only in code and
ignore quote delimiters inside comments. Do not repair only the5reported paths:
rescan all transitive dependencies because downstream capture was also hidden.

Regression cases must include apostrophes/doublequotes inside comments followed
by real imports; hash markers and escaped quotes inside strings; multiline
strings containing import-like text; actual multiline imports; and recursive
closure where a newly exposed import adds further dependencies. Preserve exact
16reviewed loader owner bytes. Capturer tests do not qualify the product loader,
TLDR resolver or compiler-owned import discovery without their own evidence.

Preserve first request/result/source/logs. Attempt2 must link the first result,
remain within the same max3 ledger, independently seal changed capture/controller
inputs, and retain separate writable roots for concurrent compilations. No old
passing criterion is rerun, no fixture is reduced, and no declaration oracle,
seed fallback or source-policy bypass is accepted.

Terminal evidence: build/native_probe/pure-loader-api-20261011-astra/ASTRA_TERMINAL_REVIEW.json.
Astra owns the bounded capturer repair and next request; root owns dispatch and
review. The full Phase1/2/3 suites, six Phase2 test executables, Phase4 binaries,
actual40worker concurrency and0.1second performance goal remain incomplete.
## Actual attempt2 qualification

Scanner7regressions passed once. Stateful full recapture adds48realdependencies,
keeps121prior dependency bytes and16loader candidate owners unchanged, and
captures169dependency files. Both real producer source closures completed120/120
without the prior missing-import errors. This establishes repair of the observed
capture omission; static inventory is not physical resolver confinement proof.

Both compilations then exitednative/raw1 in HIR, not source loading. Final HIR
error counters740/733 are counts of errors, NOT failed module counts; only20
errors each appear in returned summaries. Wall117.287/116.714seconds, peak sampled
514512/507024KiB, finalJobs0, all5961input pins unchanged. No executable produced
and no native fixture dispatched. RESULT45902a588dcd514a3c3722ae50ede18681e35c4f3cbd408f9d738b913a8f6e3c.
The HIR blocker requires causal diagnosis/reproducer before any third attempt;
no unchanged retry, source expansion by guessing, or fixture reduction is authorized.