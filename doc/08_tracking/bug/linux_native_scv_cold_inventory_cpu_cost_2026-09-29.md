# Linux native SCV cold inventory consumes minutes before a tiny entry build

Status: OPEN; measured performance problem, exact dominant function unprofiled.

## Actual retained producer and observation

Compiled source: `40ad4b3828e86f3296cf86918fa7a21ecddb195a`.
Pure Stage 2 compiler SHA256:
`9993ee84bba38cb87a7d3e296b22fa8f77fdfb12ddb5453f0047a30b05e8b35e`.
The focused source-owned first-checkout repair is `1cb396074118e`.
Its real native p2_add prime used the selected checkout, explicit cold-init
policy, core-C runtime bundle, entry closure and a private entry cache.

The existing run's native compiler child 625054 was observed at 5m57 elapsed,
5m42 CPU, 95.8% CPU and 127,544 KiB RSS. A prior complete descendant snapshot
showed the native compiler itself active under its bounded collector, without
a live Git subprocess. This establishes significant compiler-process CPU
cost, not a six-minute Git subprocess wait or high-RSS growth.
The unchanged prime bound is 600 seconds. No profiler, instrumentation,
restart, memory cap or timeout increase was used.

The attempt subsequently timed out with raw status 124 at that original
600-second bound. The supervisor finished after 614.26 seconds, raw status 1,
with 58 observed tasks and no remaining owned processes. The prime log is
empty. Canonical sanity reports frontend bootstrap-mode 0 failure 124;
bootstrap-mode 1 and ordinary probes were not run. Version and the negative
dispatch control passed. No inventory completion or admission is claimed.

Evidence root:
`/mnt/simple-bootstrap-6b2/linux-9993-scv-native-sanity-cycle1-20260929`.
Supervisor/session ownership and pins are recorded in the adjacent recovery
report `LINUX_9993_SCV_NATIVE_SANITY_CYCLE1_20260929.md`.

## Proven scope and code path

One metadata-only `git ls-tree -r -l` read at exact committed 40ad counted
compilable `.spl` and `simple.sdn` blobs, without rehashing or walking files:

| Family | Files | Committed bytes |
| --- | ---: | ---: |
| src | 17,019 | 134,168,446 |
| test | 26,764 | 166,476,024 |
| Total | 43,783 | 300,644,470 |

This excludes separately requested script roots and untracked source files;
it is the committed minimum scope added by the cold admission policy.

- `admission.spl:87–98` explicitly adds both src and test for a complete cold
  inventory, even when the requested native entry is a tiny fixture.
- `inventory_events.spl:323–344` obtains one Git listing, then serially
  reduces each compilable file to an event. `:146–183` filters non-source
  files and performs existence/read/event work for every admitted source.
- `inventory_scratch.spl:11–26` owns scratch for one file and promotes only
  its retained event, so the old all-source-text retention diagnosis does
  not describe the present implementation.
- `compile_source_inventory_core.spl:53–113` splits/trims each source line,
  normalizes whitespace, constructs canonical text, scans that text for
  three facet views, and computes five digests per file: content, semantic,
  export, initializer and provider. The minimum scope therefore calls the
  digest boundary 218,915 times before inventory publication.
- `sha256.spl:211–230` converts text to bytes and calls the native accelerator,
  with a pure fallback only for an invalid-length digest. This observation
  does not prove fallback occurred or that SHA compression dominates.
- Cold apply already uses an indexed batch, and sorting has an ordered
  linear fast path plus heap sort. Do not reintroduce old quadratic-sort or
  accumulated-event-promotion explanations without new evidence.

The proven design cost is serial repository-wide content processing before
entry compilation: at least O(total source bytes + source count), with
several allocation/conversion/facet passes. Runtime costs could add more;
the current evidence does not localize the live instruction or prove a
specific superlinear implementation defect.

## Follow-up boundary

Preserve this run and its real terminal result. Do not mask this cost by
raising the timeout or by skipping inventory/journal authority. A focused
future investigation should distinguish Git enumeration, file acquisition,
canonicalization/facet hashing, event reduction, publication/readback and
snapshot admission on the actual pure producer. Reuse genuine published
inventory for warm requests. Any optimized cold path must preserve all five
digests, src+test membership, no-follow reads, event ordering and publication
binding. Existing Windows untracked-walk evidence is related history, not
proof of the dominant Linux cost.
