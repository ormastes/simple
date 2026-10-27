# SCV BuildRunner and read-only GitHub gateway Phase 3 acceptance plan

**Execution status: NOT RUN.** The user deferred Phase 3 implementation acceptance. This document defines future oracles only; it reports no test, source compile, runtime, network, or operational PASS. Interface contracts were coordinated from isolated implementation worktrees and are not claimed as integrated or compiled in this documentation worktree. SSpec is not authored here. Its generated manual is **N/A until SSpec exists**, and neither artifact is marked complete.

## Scope and evidence model

This plan covers (1) BuildRunner source-snapshot binding and existing result/output receipt admission, and (2) a read-only GitHub gateway with strict SDN messages, gateway bearer authentication, server-side repository allowlisting, and immutable Git object reads. It does not accept write/push/PR/publication, a full GitHub tree snapshot, or a general distributed cache. The V1 GitHub protocol has `capabilities`, `read_ref`, `read_commit`, and `read_blob`; no tree enumeration method exists. A single blob cannot justify complete source scope.

Every future scenario records four separate statuses: source present, unit execution, end-to-end integration execution, and operational qualification. Source-only `VerificationReceiptV1` is never a full artifact-cache admission receipt. A passing source compile cannot be substituted for worker execution, HTTP exchange, independent output hashing, or warm/cold task-count oracles.

## BuildRunner cases

| ID | Setup/action | Required oracle | Plan mapping |
|---|---|---|---|
| BR-01 | Cold BuildRunner action from one complete frozen compile inventory; collect output bytes and actual compiler/link task counts. | Output matches independent clean-build oracle; binding names exact snapshot. Cold counts recorded, not inferred. | SCV-CACHE-21 |
| BR-02 | Repeat same action/snapshot with valid existing result and output receipts. | Identical output digests; no worker dispatch; zero relevant compiler/link tasks only if the artifact cache path is implemented and measured. | SCV-CACHE-01 |
| BR-03 | Delete published output while retaining valid task receipt/attempt. | Reuse only through existing verified local-attempt restoration; output rehashed and byte-identical. Missing artifact-store support is recorded as unavailable, never a hit. | SCV-CACHE-02 |
| BR-04 | Modify a declared source input after the prior receipt; capture a new snapshot. | Old positive witness mismatches; no warm reuse; worker sees the bytes named by the new binding or refuses. | SCV-CACHE-04 |
| BR-05 | A previously absent declared input becomes present in the requested complete snapshot. | Negative witness mismatch forces miss; no inference from ancestry or path absence outside coverage. | SCV-CACHE-09 |
| BR-06 | Unknown/partial capture coverage, missing event authority, unsupported config/external/generated input, source-relevant link, output path, or incomplete directory mapping. | Typed refusal/miss; source-only evidence does not reach `task_runner_resume` as full artifact authority. | SCV-CACHE-06, 27 |
| BR-07 | Compare unrelated/non-ancestor snapshots with add/remove/modify and directory membership changes. | Exact delta and witnesses match independent path oracle; no first-parent shortcut. | SCV-CACHE-07, 08 |
| BR-08 | Change task cache key, producer/toolchain, task input, policy/runtime/environment binding, or output digest. | Task identity or independent receipt check rejects reuse; no cross-action hit. | SCV-CACHE-24 |
| BR-09 | Corrupt/tamper a retained output or its stored digest. | Hash mismatch blocks reuse/restoration before success receipt is committed. | SCV-CACHE-17, 20 |

## Gateway protocol and service cases

| ID | Setup/action | Required oracle |
|---|---|---|
| GW-01 | Missing, malformed, wrong, or duplicate bearer credentials; request a disallowed logical repository. | Refuse before provider/`gh` calls; no bytes or cache hit leak across authorization. |
| GW-02 | Send valid `capabilities`, `read_ref`, `read_commit`, and `read_blob` requests through strict bounded SDN codec. | Response ID/repository/method/ref match exactly; status and object kind are valid; `publication=not_publication`. |
| GW-03 | Feed forged response with altered ID, repo, method, ref/OID, object kind, unknown/duplicate field, malformed status, or response over limit. | Exact response/request validator rejects; no protocol response is treated as a source witness or cache receipt. |
| GW-04 | Give invalid/corrupt/oversize base64 blob or raw bytes whose recomputed Git blob SHA-1 differs from requested OID. | Reject before returning content. Protocol SHA-256 of returned payload remains distinct from Git object identity. |
| GW-05 | Change GitHub repository identity across pre-read/read/post-read probes; use wrong numeric repository ID. | Provider refuses read; no response is bound to another owner/repository. |
| GW-06 | `read_commit` response has requested SHA field but altered raw commit bytes. | Document current limit: SHA field equality alone is not raw commit cryptographic proof; acceptance must not label it verified raw commit integrity. Future stronger proof needs a separately designed contract. |
| GW-07 | Attempt push/ref update/PR/publication method or non-`not_publication` response. | Protocol/service rejects; provider exposes reads only; no mutation is sent upstream. |
| GW-08 | Start service without supported TLS; then request wildcard/non-loopback bind or implicit plaintext. | Fail closed. Only literal loopback plus explicit development flag and reason may use plaintext; record this as development-only, never TLS PASS. |
| GW-09 | Exercise response timeout, body/line/header bounds, connection bound, unsupported GitHub host, invalid env credential reference. | Bounded typed refusal with no partial success and no secret in diagnostic output. |

## Combined handoff and acceptance evidence

- A successful GitHub `read_blob` may provide bytes for one explicit frozen file only after provider checks. It cannot create complete directory coverage or a full `ScvSnapshotV2` from current protocol methods. The combined BuildRunner/GitHub case must refuse full cache admission unless a separately approved complete inventory maps every required path to verified bytes and coverage.
- Reuse the existing compiler-owned `SemanticQueryReadManifestV1`; bind source witnesses to semantic reads only through its owning producer/validator. No BuildRunner-local duplicate manifest is acceptable.
- For warm-hit qualification, retain cold/warm output digests, independently expected symbols/runtime behavior, actual parse/HIR/MIR/OBJ/link task counts, worker dispatch count, snapshot ID, witness set/digest, receipt subject, output rehash results, HTTP request/response IDs, provider call count, refusal diagnostics, and injected fault. Do not fill these fields with fixture-declared success.
- Live GitHub checks, TLS proxy deployment, latency/RSS, and real-host network qualification are separate operational evidence. Mocked transport tests cannot satisfy them.

## Completion rule

Only after interfaces are frozen, SSpecs are written, generated manuals are reviewed, and each acceptance case actually executes may status advance beyond planned. “Source compiles,” fixture construction, a filename, or an implementation comment is not a PASS. Cases not runnable due credentials/TLS/host availability remain explicitly NOT RUN with reason and reproducible setup; do not replace them with fake passing assertions.
