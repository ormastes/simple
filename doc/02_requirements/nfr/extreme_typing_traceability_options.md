# Extreme typing and traceability: NFR options

Status: proposed extension targets awaiting selection, 2026-11-01. No
measurements exist for the new surfaces. Existing selected
[baseline NFRs](simple_traceability_sdn_slop.md), REQ-TRC-010/017 and AC-TRC-038
remain in force: warm commit p95 <=500 ms/p99 <=1 s (<=25 files/2 MiB), push
<=2 s, full hook <=10 s, report <=2 s/1000 observations, Slop <=150 ms/200 nodes,
30 samples with p50/p95/p99 per host. The options below address new workloads;
they cannot weaken selected budgets for the same baseline workload.

| Decision | Option A: benefit; cost; effort | Option B: benefit; cost; effort |
|---|---|---|
| N1 interactive budget | On a pinned 100k-node/500k-edge fixture, warm 200-row query p95 <=100 ms, CLI warm startup <=300 ms, incremental RSS <=256 MiB: comfortable interaction; compact indexes required; L. | Same fixture, p95 <=250 ms, startup <=750 ms, incremental RSS <=512 MiB: easier first delivery; more noticeable latency; M. |
| N2 compiler budget | <=5% median wall-time and <=10% peak RSS overhead for full extreme checking on the declared corpus: strong adoption target; detailed sharing/cache work; L. | <=10% median wall-time and <=20% peak RSS: simpler first implementation; higher build cost; M. |
| N3 cold indexing | 100k/500k fixture cold build <=10 s with cancellation and explicit progress: predictable use; more engineering; L. | <=30 s with the same bounded/cancelable behavior: faster delivery; delayed first query; M. |

N1's new asynchronous CodeGraph query budget is separate from the selected
loaded Slop UI response budget of 150 ms. Neither N1 option permits delaying
already-loaded UI feedback beyond the baseline target.

Hard safety contracts are not optional performance shortcuts: depth 1..8,
limit 1..200, explicit truncation/unknown, stable ordering, no automatic
network, no worktree mutation, no secret/private-path export, no side effects
before rejected publication. Work/byte/time budgets are policy fields and must
be tested against high fan-out, cycles and malformed inputs. Depth alone does
not bound fan-out or memory.

Each benchmark receipt records source revision, self-hosted binary identity,
OS/CPU/RAM, fixture digest, graph/index versions, policy digest, cold/warm
definition, samples, median/p95, peak RSS and canceled/failed work. Warm startup
excludes no required policy validation; cold fixture extraction is reported
separately. MCP/LSP startup must not import Slop/native renderer or initialize
Git/PR providers eagerly. Report realistic repository results alongside the
synthetic fixture; fixture success alone is insufficient.

Metamorphic correctness checks compare incremental/full indexing and adapter
projections on identical immutable inputs. Formal proof targets need a precise
IR refinement mapping, manually reviewed durable proof artifacts and an
explicit unsupported/blocked state. Test success is not a substitute proof.
