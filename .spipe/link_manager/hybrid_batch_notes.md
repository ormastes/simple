# Hybrid batch shapes — design notes (Wave-7 prep, Lane HYBRID, wave 6)

**Date:** 2026-07-31 · **Status:** Preparatory notes only — the batch-layout
freeze itself stays **deferred** per contract §6 ("Reachability frontier /
constraint-propagation batch layouts … frozen with the hybrid wave against
real batch shapes", `link_manager_contract_v1.md:110-111`). This document
prepares that freeze; it does not perform it.

**Sources (verified in-tree):**
- Plan Wave 7: "GPU hash/sort/resolve/reachability/scan/relocation batches;
  CPU decode/control" (`doc/03_plan/platform/structural_compute/link_manager_plan.md:48-49`).
- Contract §3 wire layouts (`doc/05_design/platform/structural_compute/link_manager_contract_v1.md:39-46`):
  ResolveKey **20 B** (Hash128 16 + space u32), DefinitionRecord **44 B**
  (`SDFN`: key 20 + owner EntityRef 8 + attributes u64 + order u64),
  ReferenceRecord **44 B** (`SRFR`, same layout), ResolutionRecord **20 B**
  (`SRSL`: reference 8 + definition 8 + status u8 + reason u8 + reserved u16
  == 0). Verified against the doc, not this lane's prompt.
- CPU primitives: `src/lib/common/structural/resolve/resolve_core.spl`,
  `resolve_frontier.spl`; oracle codec `resolve_codec.spl`.
- Placement surface: `src/lib/common/compute/placement_contracts/backend.spl`
  (`StageReceipt` :9, `PlacementLease`/`LeaseSet` :44-51, `PlacementBackend`
  trait :76-83), `semantic.spl` (`Hash256` :27, `StageId` :30,
  `ExecutionMode` :36).
- Stage ids: `SMF_LINK_STAGE_L0_DISCOVER … L12` as `i64` values 0-12
  (`src/lib/common/structural/resolve/resolve_types.spl:275` ff., contract §4
  `link_manager_contract_v1.md:81-83`).
- Parity harness precedent: `.spipe/link_manager/smf_linker_map.md` §5
  (`smf_linker_map.md:230-283`).

## 1. CPU primitive inventory (what each batch must reproduce)

| Primitive | Location | Algorithm (as shipped) |
|---|---|---|
| `intern_name(text) -> Hash128` | `resolve_core.spl:41` | SHA-256 of the name bytes; first 16 digest bytes become hi/lo, 8 B each, assembled LE via `_digest_u64_le` (`resolve_core.spl:55`), mirroring `wire.spl#wire_get_u64` byte order |
| `sort_definitions_stable` / `sort_references_stable` | `resolve_core.spl:105` / `:153` | dedicated stable merge sort; full lexicographic key `(name_hash.hi, name_hash.lo, space, order)` per `_def_key_le`/`_ref_key_le` (`resolve_core.spl:75`, `:123`); merge takes the left run on ties (`resolve_core.spl:66-72` comment) |
| `group_sorted(defs, refs) -> [ResolveGroupView]` | `resolve_core.spl:182` | two-pointer scan over the two sorted arrays; one view per distinct key in ascending key order; views carry `definitions_offset/count`, `references_offset/count` as u32 (`resolve_core.spl:211-216`) |
| `reduce_group(view, defs) -> ResolveGroupResult` | `resolve_core.spl:223` | 0 defs → Unresolved/MissingDefinition + zero EntityRef; 1 def → Resolved/Unspecified; ≥2 → Resolved to lowest-`order` def (first slot) + reason DuplicateDefinition + `diagnostic_count = definitions_count - 1` (`resolve_core.spl:240-260`, contract §7 item 6) |
| `reachable_mark(node_count, edges, roots) -> ReachableResult` | `resolve_frontier.spl:111` | worklist BFS over `ResolveEdge {from_index, to_index}` u32 pairs (`resolve_frontier.spl:32-37`); bounds-reject up front (`:112-117`); output `values: [bool]` |
| `propagate_constraints(node_count, edges, initial) -> ConstraintPropagationResult` | `resolve_frontier.spl:176` | Jacobi-style full-pass fixpoint: `next[i] = values[i] | OR(values[from])` over incoming edges (`_propagate_once`, `resolve_frontier.spl:154`); cap `edges.len() + 1` (`:184`); cap-hit is explicit `ok=false`, never partial success (`:194-195`) |

## 2. Batch stage mapping

Common bracket for every batch (placement_contracts, frozen at gpu_mmu
`75e6b1e8435b`, contract §2 `link_manager_contract_v1.md:32-35`):

```
plan(requests, budget) -> PlacementPlan        # backend.spl:78
acquire(plan) -> Result<LeaseSet, ...>         # backend.spl:79
[optional prefetch(plan)]                      # backend.spl:80
  ... run batch against leased device ranges (PlacementLease.device_address/
      length, backend.spl:44-48) ...
release(leases)                                # backend.spl:82
emit StageReceipt                              # backend.spl:9-23
```

`StageReceipt` fields available: `stage: StageId`, `backend`, `mode:
ExecutionMode` (CpuReference/HybridVectorGpu/ResidentGpu, `semantic.spl:36-39`
— mirrors contract §3 `ResolveMode`), `input_root`/`output_root`/
`deterministic_hash: Hash256`, `item_count_in/out`, `bytes_read/written`,
`fallback_count`, `malformed_count`, `overflow_flags`, `elapsed_us`
(`backend.spl:9-23`). Hybrid batches set `mode = HybridVectorGpu`; the parity
oracle run sets `mode = CpuReference`.

### 2.1 hash batch  ←  `intern_name`  (stage `SMF_LINK_STAGE_L3_INTERN_SORT` = 3, `resolve_types.spl:278`)

- **Input (CPU-prepared):** variable-length name bytes flattened to a byte
  blob + `[u32]` offsets array + `[u32]` lengths (or offsets of n+1 entries).
  Element widths: blob u8; offsets 4 B. This layout is NOT frozen anywhere —
  open question Q5.
- **Output:** `[Hash128]`, 16 B/element (hi u64 | lo u64, LE per
  `resolve_core.spl:45-48`); CPU then attaches the profile's `space: u32` to
  form 20 B `ResolveKey`s (contract §3 row 1). Space assignment stays CPU —
  it is profile semantics (e.g. `smf_collect_records`,
  `src/compiler/70.backend/linker/gpu_smf/smf_link_profile.spl:115`).
- **Stays CPU:** SMF decode producing the names (L1), space selection,
  record assembly into 44 B Definition/ReferenceRecords.
- **Parity (§5.3):** the GPU SHA-256/truncate must byte-match
  `intern_name` — same first-16-bytes-LE assembly. Gate: encode the resulting
  DefinitionRecord/ReferenceRecord arrays via `encode_definition_record` /
  `encode_reference_record` (`resolve_codec.spl:165`, `:179`) and hash;
  compare against the CPU-path hash (contract §5.3,
  `link_manager_contract_v1.md:91-92`).

### 2.2 sort batch  ←  `sort_definitions_stable` / `sort_references_stable`  (stage L3 = 3)

- **Input:** the two record arrays, 44 B/element (contract §3 rows 2-3), or —
  preferable on GPU — a 28 B extracted sort key per record (hi u64 + lo u64 +
  space u32 + order u64) plus the original index u32, sorting a permutation
  instead of moving 44 B payloads. Which representation the freeze picks is
  open question Q8.
- **Output:** the records in `(hi, lo, space, order)` ascending order; if
  permutation-sorted, `[u32]` permutation applied CPU-side.
- **Stability requirement:** the CPU sort is stable by construction
  (`resolve_core.spl:66-72`); a GPU radix/merge sort must preserve original
  relative order for fully-equal keys (LSD radix or index-as-final-tiebreak
  both satisfy this and are byte-indistinguishable from stable order because
  the tiebreak key includes the original index).
- **Stays CPU:** nothing semantic; control + permutation apply only.
- **Parity:** serialized sorted-record stream (44 B × n) byte-matches the CPU
  sorted stream via the §5.3 hash gate.

### 2.3 resolve batch  ←  `group_sorted` + `reduce_group`  (stage `SMF_LINK_STAGE_L4_SELECT` = 4, `resolve_types.spl:279`)

- **Input:** the two sorted 44 B arrays from the sort batch.
- **Intermediate:** group boundaries. On CPU this is `[ResolveGroupView]`
  (`resolve_types.spl:227`, built at `resolve_core.spl:211-216`). Contract §4
  lists `ResolveGroupView` among in-memory arena handles, "never wire
  records" (`link_manager_contract_v1.md:76-79`), so a GPU boundaries array
  (e.g. `[u32]` head-flags → segment offsets via scan) is a new batch-only
  layout — part of the deferred freeze (Q10).
- **Output:** per-group results, then `[ResolutionRecord]` 20 B/element
  (contract §3 row 4). Reduction is trivially parallel per group: winner =
  first def slot of the group (lowest order, since sort key ends in `order`),
  status/reason/diagnostic_count per `resolve_core.spl:240-260`.
- **Stays CPU:** materializing per-reference ResolutionRecords with the
  profile's status semantics (e.g. `smf_resolve`,
  `smf_link_profile.spl:157`), diagnostic reporting order, and the archive
  fixpoint loop L5 (`SMF_LINK_STAGE_L5_ARCHIVE_FIXPOINT` = 5,
  `resolve_types.spl:280`) which re-enters collect/resolve — the loop is
  control flow, CPU-owned.
- **Parity:** `encode_resolution_record` (`resolve_codec.spl:193`) over the
  batch output must byte-match the CPU pipeline's encoded stream, including
  `reserved u16 == 0` (`resolve_codec.spl:157`).

### 2.4 reachability batch  ←  `reachable_mark` + `propagate_constraints`  (stage `SMF_LINK_STAGE_L6_REACHABILITY` = 6, `resolve_types.spl:281`)

- **Input:** `[ResolveEdge]` — in-memory u32 pair, 8 B/edge if packed
  (`resolve_frontier.spl:32-37`); `[u32]` roots; for constraints `[u64]`
  initial values, 8 B/node. No frozen wire layout exists for any of these —
  exactly the §6 deferral. A CSR adjacency (edge array sorted by `to_index`
  for the gather in `_propagate_once`, by `from_index` for BFS scatter) is
  the natural batch form; raw-edge-list vs CSR is open question Q3.
- **Output:** reachability marks — CPU produces `[bool]`
  (`resolve_frontier.spl:43-49`); GPU representation (u8 vs u32 vs bitset) is
  open question Q4. Constraint output `[u64]`, 8 B/node, plus `iterations`
  scalar (`resolve_frontier.spl:51-58`).
- **GPU shape:** `_propagate_once` is already Jacobi (reads only previous
  state, `resolve_frontier.spl:142-151` comment) → one gather kernel per
  pass; convergence check = parallel reduce of `next != prev`; cap
  `edges.len() + 1` enforced by the CPU control loop, cap-hit → explicit
  batch failure mirroring `ok=false` (`:194-195`). BFS becomes
  frontier-parallel level iterations; the CPU worklist order
  (`resolve_frontier.spl:103-108`) does not affect the final marks (monotone
  set growth), so parity is defined on the final marks/values arrays, not on
  visit order.
- **Stays CPU:** building the section-edge graph and root set (profile
  semantics: `smf_reachable_sections`,
  `src/compiler/70.backend/linker/gpu_smf/smf_reachability.spl:34`), the
  bounds pre-check (`resolve_frontier.spl:64-76` discipline), and
  dead-strip application (`smf_unreachable_symbol_indices`,
  `smf_reachability.spl:49` — stable input order, defined-symbols-only).
- **Parity:** marks and constraint-value arrays, serialized in a
  to-be-frozen canonical encoding, byte-match the CPU arrays; `iterations`
  need not match (Jacobi pass count is identical anyway, but the freeze
  should say so explicitly — folded into Q3/Q4).

### 2.5 scan batch  ←  **no CPU primitive yet**  (stage `SMF_LINK_STAGE_L7_ADDRESS_LAYOUT` = 7, `resolve_types.spl:282`)

- Plan scope names "scan-based placement" (`link_manager_plan.md:10-11`) but
  neither `resolve_core.spl` nor `resolve_frontier.spl` ships a prefix-sum /
  placement primitive, and the smf map records "no current equivalent" for
  intern/sort-adjacent structure (`smf_linker_map.md:158`) with L7-L9
  currently performed by the external clang process in the verified harness
  run (`smf_linker_map.md:271-277`).
- **Expected shape (for the freeze):** input `[u64]` sizes + `[u64]`
  alignments per section/symbol; exclusive prefix-sum with align-up →
  `[u64]` offsets. Stays CPU: section ordering policy (profile-driven,
  `link.hot_order` / `link.output_range` tags, contract §4
  `link_manager_contract_v1.md:83-84`).
- **Blocked on Q6:** the CPU reference (oracle) must land before any batch
  parity can be defined. Receipt stage id L7.

### 2.6 relocation batch  ←  **no CPU primitive yet**  (stage `SMF_LINK_STAGE_L8_RELOCATION` = 8, `resolve_types.spl:283`)

- Same status as scan: relocation application today lives behind the
  `link_native_cc`/clang fallback in the verified parity run
  (`smf_linker_map.md:271-277`); no `resolve/*` primitive exists.
- **Expected shape:** input relocation records (site offset u64 | symbol
  index u32 | kind u32 | addend i64 — widths illustrative, NOT frozen) +
  resolved address table `[u64]`; output = patched code bytes or a patch
  list (site u64 | value u64). MutationOp/MutationPlan wire encoding is
  MUTATE-lane owned (contract §6, `link_manager_contract_v1.md:96-97`) —
  the relocation batch layout must not pre-empt it; LINK emits only
  `LinkMutationKind` 1 AddRelocation (contract §3,
  `link_manager_contract_v1.md:57`). Receipt stage id L8. Blocked on Q6.

## 3. Parity gate summary (§5.3 applied per batch)

Contract §5.3: "The CPU reference codec is the oracle and is never deleted;
hybrid/resident encoders must produce byte-identical output (acceptance:
parity by hash)" (`link_manager_contract_v1.md:91-92`). Concretely per batch:
run the CPU primitive and the GPU batch on identical inputs; serialize both
outputs through the frozen codec (`encode_definition_record:165`,
`encode_reference_record:179`, `encode_resolution_record:193` in
`resolve_codec.spl`; frontier arrays via the to-be-frozen batch encoding);
`sha256` both streams; equality is the gate — the same run-twice-and-hash
discipline the SMF harness already demonstrated end-to-end
(`smf_linker_map.md:259-269`). The hashes land in `StageReceipt.output_root`
/ `deterministic_hash` so the check is receipt-auditable across modes
(`backend.spl:13-14,23`); comparing the CpuReference receipt's roots against
the HybridVectorGpu receipt's roots for the same stage id IS the acceptance
check ("CPU/hybrid/resident parity by hash", `link_manager_plan.md:56`).

## 4. Open questions for the freeze

1. **StageId is text-valued** (`semantic.spl:30-31`) while
   `SMF_LINK_STAGE_L*` are `i64` 0-12 (`resolve_types.spl:275` ff.). The
   freeze needs the canonical mapping convention (e.g. `"smf.link.L3"`)
   without changing either frozen contract. (Wave-6 Lane PROFILE's
   `smf_link_receipts.spl` will face this first — align with whatever it
   lands.)
2. **`StageReceipt.elapsed_us: u64`** (`backend.spl:22`) is inherently
   nondeterministic, but receipts must be deterministic (LANE_GUIDE wave-6
   PROFILE: "counts/hashes — no timestamps", `LANE_GUIDE.md:105-107`).
   Convention needed: zero it, or exclude it from `deterministic_hash`.
3. **Edge-array batch layout:** raw `[ResolveEdge]` 8 B pairs vs CSR
   (row-offsets + column-indices) — and whether `iterations` parity is
   required. Contract §6 defers exactly this; freeze against real shapes.
4. **Reachability marks representation:** CPU `[bool]`
   (`resolve_frontier.spl:49`) has no wire codec at all; the batch needs a
   canonical serialization (u8-per-node vs bitset) before a byte-parity gate
   can even be stated.
5. **Variable-length name blob layout** for the hash batch (offsets/lengths
   + byte blob) is unfrozen; it is the only batch input that is not a
   fixed-width record array.
6. **Scan (L7) and relocation (L8) have no CPU reference primitive** in
   `src/lib/common/structural/resolve/` — the oracle must exist before the
   batch freeze can define parity for them; today those stages run inside
   external clang in the only verified harness path
   (`smf_linker_map.md:271-277`).
7. **`Hash256.value: text`** (`semantic.spl:27-28`): the freeze must pin the
   canonical text encoding (lowercase hex of sha256, presumably) so
   `input_root`/`output_root` comparisons are well-defined across backends.
8. **Sort batch representation:** move 44 B records vs sort a 28 B key +
   u32 index permutation. Parity is defined on the reordered record stream
   either way; the freeze must still pick one so `bytes_read/bytes_written`
   receipt fields are comparable.
9. **Lease granularity across the L5 archive fixpoint:** one `LeaseSet`
   spanning L3-L8 vs per-batch acquire/release — and what a `StaleLease`
   error (`backend.spl:70`) means mid-fixpoint (retry the pass vs fail the
   link). placement_contracts has no re-validate/renew call; if renewal is
   needed it is a gap to raise, not a contract change to propose.
10. **Group-boundaries array:** contract §4 forbids `ResolveGroupView` as a
    wire record (`link_manager_contract_v1.md:76-79`); the GPU segment
    layout (head-flags/offsets) is therefore a new batch-only layout that
    must be named as such in the freeze, distinct from the frozen in-memory
    struct at `resolve_types.spl:227`.
