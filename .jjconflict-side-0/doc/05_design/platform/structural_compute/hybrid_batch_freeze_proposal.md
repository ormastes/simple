# Hybrid Batch-Layout Freeze Proposal (Lane FREEZEPROP, wave 8)

**Date:** 2026-08-01 · **Status:** PROPOSAL ONLY — nothing here is applied.
The contract doc `link_manager_contract_v1.md` is NOT edited by this lane;
§6 still defers the batch-layout freeze ("Reachability frontier /
constraint-propagation batch layouts … frozen with the hybrid wave against
real batch shapes", `link_manager_contract_v1.md:110-111`).

**Inputs:** the 10 open questions in
`.spipe/link_manager/hybrid_batch_notes.md:204-247`; the now-**measured**
columnar shapes in `src/lib/common/structural/resolve/resolve_batch.spl`
(landed, in-memory only per its own scope note `resolve_batch.spl:10-14`);
the landed receipt conventions in
`src/compiler/70.backend/linker/gpu_smf/smf_link_receipts.spl`; the landed
L8 formula oracle `smf_reloc_formulas.spl`; contract §3 widths
(`link_manager_contract_v1.md:39-59`), §5 versioning (`:86-92`), §6
deferrals (`:94-111`); plan Wave 7 (`link_manager_plan.md:48-49`) and
Wave 9 (`:50-51`).

**Labels:** DECIDE-HERE = safe to freeze from landed evidence alone.
ARCH-OWNER = requires a human/architecture decision before freezing.

---

## Q1 — StageId text vs i64 stage keys

**Question (notes:206-211):** `StageId` is text-valued (`semantic.spl:30-31`)
while `SMF_LINK_STAGE_L*` are `i64` 0-12 (`resolve_types.spl:275` ff.); the
freeze needs the canonical mapping without changing either frozen contract.

**Recommendation:** Ratify the landed mapping
`smf_link_stage_id(stage) -> StageId(value: "smf_link.L" + stage.to_text())`
(`smf_link_receipts.spl:66-71`), generalized as `<profile>.<stage-name>`
text keys — wave-8 Lane STYLERCPT uses the same pattern
(`"style_link.<stage>"`, LANE_GUIDE wave-8 STYLERCPT block). Both frozen
contracts stay untouched: profiles own the text spelling; the i64 consts
remain the in-memory pipeline keys.

**Label: ARCH-OWNER.** The convention is landed in one profile, but making
`<profile>.<stage>` normative across all future profiles (SMF, style, clang
offload) is a cross-contract naming decision the architecture owner must
sign, exactly as the lane guide flags ("StageId text vs i64").

## Q2 — `StageReceipt.elapsed_us` determinism policy

**Question (notes:212-215):** `elapsed_us: u64` (`backend.spl:22`) is
nondeterministic, but receipts must be deterministic; zero it or exclude it
from `deterministic_hash`?

**Recommendation:** Ratify the landed convention: `elapsed_us: 0` always
(`smf_link_receipts.spl:188`; header comment `:20` states elapsed_us /
bytes_read / bytes_written are always 0 in the deterministic wrappers).
`deterministic_hash` is computed only over content serializations via
`sha256_text` (`smf_link_receipts.spl:167-175`), so timing never enters any
hash. If real timing is ever wanted, it must ride a separate
non-deterministic side channel, not the receipt.

**Label: ARCH-OWNER.** Zeroing discards data a future profiler may want;
choosing "zeroed field" over "excluded-from-hash but populated" is a policy
call across every placement_contracts consumer (gpu_mmu freeze
`75e6b1e8435b`, contract §2 `link_manager_contract_v1.md:32-35`), flagged
by name in the lane guide as an ARCH-OWNER example.

## Q3 — Edge-array batch layout: raw pairs vs CSR; `iterations` parity

**Question (notes:216-218):** raw `[ResolveEdge]` 8 B pairs vs CSR
(row-offsets + column-indices), and whether `iterations` parity is required.

**Recommendation:** Freeze the **batch input** as two u32 columns
`from_index: [u32]`, `to_index: [u32]` — the direct columnar (SoA) form of
the landed `ResolveEdge {from_index: u32, to_index: u32}`
(`resolve_frontier.spl:32-37`), matching the one-array-per-field discipline
resolve_batch.spl landed for records (`resolve_batch.spl:56-65`). CSR is
permitted as a backend-internal *derived* form, never parity-visible.
`iterations` (`resolve_frontier.spl:58`) is **excluded from parity**:
parity is defined on final marks/values only, because CPU worklist visit
order does not affect final marks (notes:141-145) and the Jacobi cap-hit
path already fails explicitly (`resolve_frontier.spl:194-195` per
notes:139-141) rather than returning a partial state.

**Label: DECIDE-HERE.** Both halves follow mechanically from landed shapes
(`resolve_frontier.spl` structs + resolve_batch's SoA precedent).

## Q4 — Reachability marks serialization

**Question (notes:219-222):** CPU marks are `[bool]`
(`resolve_frontier.spl:49`) with no wire codec; the batch needs a canonical
serialization (u8-per-node vs bitset) before byte parity can be stated.

**Recommendation:** Freeze **u8-per-node**, values strictly 0 or 1, any
other byte = hard reject. Rationale: the wire contract already standardizes
u8 discriminants with unknown-value hard reject (contract §2
`link_manager_contract_v1.md:30-31`, §3 enums `:48`), and the frontier
module's own discipline is explicit-reject-not-trap
(`resolve_frontier.spl:25`). A bitset saves 8x space but introduces a new
bit-order convention with no landed precedent; nothing landed motivates it.

**Label: DECIDE-HERE.**

## Q5 — Variable-length name-blob layout for the hash batch

**Question (notes:223-225):** the offsets/lengths + byte-blob layout for
the only non-fixed-width batch input is unfrozen.

**Recommendation:** Freeze exactly the **measured** landed shape
`NameBatch { blob: [u8], offsets: [u32] }` (`resolve_batch.spl:46-50`) with
its landed discipline: `offsets.len() == names.len() + 1`, `offsets[0] == 0`,
`offsets[last] == blob.len()`, element i spans
`blob[offsets[i] .. offsets[i+1]]`, UTF-8 segments
(`batch_flatten_names`, `resolve_batch.spl:90-108`); rebuild hard-rejects
broken offset discipline or invalid UTF-8, never traps
(`batch_rebuild_names`, `resolve_batch.spl:110-129`). This drops the
"separate lengths array" alternative from notes:66-69 — n+1 offsets landed
and is asserted round-trip-exact against the frozen codec by
resolve_batch_spec (scope note `resolve_batch.spl:12-14`).

**Label: DECIDE-HERE.** This is the strongest row: the shape is landed,
spec-verified, and byte-parity-anchored to the frozen oracle codec.

## Q6 — Scan (L7) and relocation (L8) CPU reference oracles

**Question (notes:226-230):** L7/L8 have no CPU reference primitive; the
oracle must exist before batch parity can be defined for them.

**Recommendation:** Treat as **conditionally resolved by wave 8 — verify at
landing.** The L8 *formula* oracle is already landed:
`smf_reloc_compute(reloc_type, s, a, p) -> SmfRelocValue { ok, value }`
(`smf_reloc_formulas.spl:93-102`), total over `RelocationType` with
out-of-width reject-not-truncate (`:46`, `:99`) and a wire-value dispatcher
(`smf_reloc_compute_wire`, `:116-131`). Wave-8 Lane APPLY
(`smf_reloc_apply.spl`, all-or-nothing patch with `rejected_index`) and
Lane LAYOUT (`smf_section_layout.spl`, align-up prefix scan with overflow
reject) complete the L8 applier and L7 scan oracles per the wave-8 lane
guide; as of this writing neither file exists in the WC yet, so the freeze
must gate on their landed specs, not on the lane-guide text. Only after
both land can §5.3-style parity ("byte-identical output … parity by hash",
`link_manager_contract_v1.md:91-92`) be stated for L7/L8 batches.

**Label: DECIDE-HERE** (conditional on wave-8 APPLY/LAYOUT landing green;
no architecture judgment is pending — only landing verification).

## Q7 — `Hash256.value: text` canonical encoding

**Question (notes:231-233):** the freeze must pin the canonical text
encoding of `Hash256.value` (`semantic.spl:27-28`) so root comparisons are
well-defined across backends.

**Recommendation:** Freeze **64-character lowercase hex of SHA-256**. This
is what is already landed and flowing into receipts: `sha256_text` returns
a 64-char lowercase hex string (`src/lib/common/crypto/sha256.spl:170`,
fn at `:188`) and `_smf_stage_receipt` feeds those hex strings directly
into `input_root`/`output_root`/`deterministic_hash`
(`smf_link_receipts.spl:162-175`). Freezing anything else would break the
landed receipts.

**Label: DECIDE-HERE.**

## Q8 — Sort batch representation: move 44 B records vs key+index permutation

**Question (notes:234-237):** sort the 44 B records, or a 28 B extracted
key + u32 original index permutation; receipts' `bytes_read/bytes_written`
must be comparable either way.

**Recommendation:** Freeze **permutation sort over the columnar batch**:
the sort key columns `(name_hash_hi, name_hash_lo, space, order)` are
already four of the seven landed columns in
`DefinitionBatch`/`ReferenceBatch` (`resolve_batch.spl:56-65`, `:71-80`) —
no extraction step is needed; the batch sorts a `[u32]` index array with
original index as final tiebreak, which is byte-indistinguishable from the
CPU stable sort (notes:93-97; CPU key order `(hi, lo, space, order)` with
left-run-on-ties per `_def_key_le`/`_ref_key_le`,
`resolve_core.spl:69-75`, `:123`). Permutation apply stays CPU-side
(notes:92). Receipt accounting: `bytes_read` = key columns read (28 B x n),
`bytes_written` = 4 B x n permutation — comparable because the
representation is now fixed. Moving 44 B AoS records would contradict the
landed SoA measurement groundwork.

**Label: DECIDE-HERE.**

## Q9 — Lease granularity across the L5 archive fixpoint

**Question (notes:238-242):** one `LeaseSet` spanning L3-L8 vs per-batch
acquire/release, and what `StaleLease` (`backend.spl:70`) means
mid-fixpoint (retry the pass vs fail the link).

**Recommendation:** Recommend **per-batch acquire/release** as the v1
baseline — it is the only flow the frozen trait expresses
(`plan/acquire/[prefetch]/release`, `backend.spl:78-82`) — with
`StaleLease` mid-fixpoint = fail the whole link step explicitly (mirroring
the frontier's cap-hit ok=false discipline, `resolve_frontier.spl:25`).
But placement_contracts has **no re-validate/renew call**, and the notes
correctly classify a renewal need as "a gap to raise, not a contract change
to propose" (notes:241-242). Whether a spanning lease (performance across
the L5 re-entry loop, `resolve_types.spl:280`, notes:117-120) justifies
extending the frozen gpu_mmu trait is precisely that gap.

**Label: ARCH-OWNER.** Retry-vs-fail policy and any lease-renewal surface
touch the frozen placement contract owned outside the LINK lane.

## Q10 — Group-boundaries batch layout (ResolveGroupView is not wire)

**Question (notes:243-247):** contract §4 forbids `ResolveGroupView` as a
wire record (`link_manager_contract_v1.md:76-79`); the GPU segment layout
must be named as a distinct batch-only layout.

**Recommendation:** Freeze a **named batch-only layout**
`GroupBoundaryBatch { group_offsets: [u32] }` with `len == groups + 1`,
`group_offsets[0] == 0`, monotone non-decreasing, final element == element
count — the exact n+1 offsets discipline the landed `NameBatch` uses,
including its hard-reject validation on rebuild
(`resolve_batch.spl:46-50`, `:118-129`). One offsets array per record kind
(definitions, references) reproduces `ResolveGroupView`'s
`definitions_offset/count`, `references_offset/count` u32 fields
(notes:105-106, built at `resolve_core.spl:211-216`) without ever
serializing the in-memory struct (`resolve_types.spl:227`). The name marks
it batch-only, distinct from the frozen arena handle, as §4 requires.

**Label: DECIDE-HERE.** It reuses a landed, spec-verified layout discipline
and creates no new convention.

---

## Tally

- **DECIDE-HERE:** Q3, Q4, Q5, Q6 (conditional on wave-8 landing), Q7, Q8,
  Q10 — 7 rows.
- **ARCH-OWNER:** Q1 (StageId mapping normativity), Q2 (elapsed_us policy),
  Q9 (lease granularity / StaleLease / renewal gap) — 3 rows.

---

## PROPOSED §6 amendment — NOT APPLIED

The following text WOULD replace the final §6 bullet of
`link_manager_contract_v1.md` (currently `:110-111`) **if and only if**:
(a) the three ARCH-OWNER rows above are decided, and (b) wave-8 Lanes
APPLY/LAYOUT land green (Q6 verification). Until then the deferral stands.
This lane does not edit the contract doc.

> ```
> - ~~Reachability frontier / constraint-propagation batch layouts~~ —
>   **frozen** (hybrid wave, batch schema v1): see
>   `src/lib/common/structural/resolve/resolve_batch.spl` for the measured
>   columnar shapes. Frozen batch layouts (in-memory SoA for hybrid stages;
>   the §3 wire codec remains the sole oracle and parity gate per §5.3):
>   - Name blob: `NameBatch { blob: [u8], offsets: [u32] }`, offsets.len ==
>     names + 1, offsets[0] == 0, final offset == blob.len(), UTF-8
>     segments; rebuild hard-rejects malformed shape.
>   - Record columns: `DefinitionBatch` / `ReferenceBatch` — one array per
>     frozen §3 field (name_hash_hi u64 | name_hash_lo u64 | space u32 |
>     owner_object_slot u32 | owner_local_index u32 | attributes u64 |
>     order u64); ragged batches hard-reject.
>   - Edges: `from_index: [u32]`, `to_index: [u32]` (SoA of ResolveEdge);
>     CSR is backend-internal and never parity-visible.
>   - Reachability marks: u8-per-node, 0/1 only, other values hard-reject.
>     `iterations` is excluded from parity; parity is final marks/values.
>   - Group boundaries: `GroupBoundaryBatch { group_offsets: [u32] }`,
>     len == groups + 1, offsets discipline as NameBatch; batch-only —
>     `ResolveGroupView` remains an arena handle, never serialized (§4).
>   - Sort batches sort a [u32] permutation over the key columns
>     (hi, lo, space, order; original index as final tiebreak); permutation
>     apply is CPU-side; receipts account 28 B x n read, 4 B x n written.
>   - `Hash256.value` in receipts is 64-char lowercase hex of SHA-256.
>   - StageId mapping and elapsed_us policy: per ARCH-OWNER decision
>     [placeholder — insert decided text; landed precedent is
>     "smf_link.L<n>" and elapsed_us == 0].
>   Any change bumps the batch schema version per §5 rule 1.
> ```

**End of proposal. Nothing above is in force.**
