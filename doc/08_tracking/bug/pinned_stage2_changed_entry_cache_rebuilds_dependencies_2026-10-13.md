# Pinned Stage 2 changed-entry cache rebuilds the dependency fixture

Status: OPEN native qualification blocker. This report concerns producer SHA256 `4812f6ed17fe51ef0bd36fdd5d6f02d2871d7f6c14a9b468bed209016f33be77`, not an untested claim about a rebuilt current-source compiler.

The native-cache integration fixture was copied into a private project with unchanged `util_a.spl` and `util_b.spl`. Cold generation 0 compiled and ran `hello cache 42`. The controlled generation 1 -> 2 pair changes only the entry body from `double(22)` to `double(23)` and produces the expected outputs 44 and 46. Both controlled generations report `Cache: reused 0 modules; rebuilt 5.` They use the same frozen producer, backend, target, runtime/provider, cache path, entry path and observer filenames. Exclusive observer files are archived before recreation. Neither helper source changed.

Cold wall time was 18.9605 seconds. Controlled generations took 3.5609 and 3.6294 seconds including linking. These are not SPL-to-object p95 samples, a speedup claim or a prepared TLDR acceptance result. No 100 ms claim is supported.

The retained cache index after generation 2 contains one source row (the entry) and an empty module witness. The cache has 3 scope directories. These observations show that this pinned path does not establish unchanged dependency object reuse; they do not prove which identity, persistence or witness defect caused the misses. Current source has newer stable-scope/per-module-witness logic, so qualification needs the coherent successor before any repair is accepted. Never weaken a witness or rewrite identities to force a hit.

An initial changed-entry observer refusal is retained separately: reusing the exclusive memory-snapshot file was correctly rejected. A subsequent comparison changed observer paths and is not by itself a controlled cache-scope comparison. The final generation 1 -> 2 pair corrects that confound.

Evidence: `.simple/storage/build/phase3-incremental-completion/changed-entry-cache/`, including generation source snapshots, argv, logs, resource/watchdog receipts, real program output, before/after cache indexes and `evidence/controlled-summary.json`. No unchanged passing run was replayed. This bounded diagnostic is closed; no fourth equivalent automatic cycle.

Recovery owner: Codex phase3-incremental-completion lane. First qualify the Stage 3 successor, then connect the actual summary/MIR consumer and complete cache witnesses, preserve valid dependency artifacts, and qualify the exact changed-entry workload and negative invalidation controls. Relevant requirements: REQ-IM-005/006/008/016 and NFR-IM-001/002.

## Identity investigation without another replay

All 9 retained HIR cache frames have the same frontend identity header, binding the frozen executable SHA256 and frontend-source fingerprint. The retained Stage 2 admission receipt reports the matching candidate digest, admitted status and v1 ABI policy. These static observations do not establish that native object producer identity admitted the receipt, that complete module witnesses were persisted, or that semantic graph inputs were stable. They narrow the next investigation to actual cache-key composition, witness persistence and acceptance diagnostics rather than accepting an arbitrary identity override. Details: `changed-entry-cache/evidence/cache-identity-observations.json`.
