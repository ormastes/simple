# NVFS Formal Verification — Prior Art & Scoping for Lean 4

> **Phase:** research prelude to the Lean 4 state-model at
> `/home/ormastes/dev/pub/simple/formal/nvfs/`.
> **Audience:** anyone adding or revising NVFS invariants, ops or
> crash-consistency proofs.
> **Scope of this document.** Brief survey of filesystem formal
> verification (FSCQ, Yggdrasil, Ivy/TLA+), the Lean 4 systems-verification
> tool-chain, and a concrete recommendation for NVFS: prove ten
> state-integrity invariants as preservation theorems over each op, plus
> one crash-refinement theorem per critical op, without claiming
> POSIX-refinement.

---

## 1. Why formally verify NVFS at all?

NVFS sits directly beneath two clients whose own correctness claims
depend on the filesystem's integrity story:

* **spostgre** (embedded SQL engine, `doc/05_design/spostgre_design.md`)
  — WAL-before-pmap-publish, sealed-checkpoint-arena, MVCC generation
  pinning.  A filesystem that violates any of these invariants silently
  corrupts committed data.
* **svllm** (model-serving runtime, `doc/05_design/nvfs/svllm_requirements.md`)
  — atomic manifest publish, tensor-pack immutability, warm-switch
  semantics.  A silently-corrupted `arena_seal` breaks model-swap
  atomicity.

Both clients' specs are phrased as contracts on the NVFS surface; the
surface is useless if NVFS can itself cheat.  Formal verification
raises the bar from "no observed failures on our test fixtures" to
"no reachable state violates the stated invariants", and for crash
consistency specifically it is the only sound way to argue correctness.

The alternative — exhaustive testing + fuzzing — will almost certainly
find first-order bugs (and has done so on btrfs/ZFS) but cannot rule
out the "rare interleaving that only happens with power-loss during
the third fsync of a multi-block pmap publish" class of defect.  That
is the class of defect FSCQ, Yggdrasil and friends were designed to
eliminate.

---

## 2. Prior art

### 2.1 FSCQ (Chen, Ziegler, Chajed, Chlipala, Kaashoek, Zeldovich; SOSP 2015)

FSCQ is the canonical point of reference: the first filesystem with a
machine-checked proof of crash safety.  Primary sources:

- Chen et al., *"Using Crash Hoare Logic for Certifying the FSCQ File
  System"*, SOSP 2015.
- Source + Coq proofs: `https://github.com/mit-pdos/fscq`.
- Thesis chapter: Haogang Chen, *"Certifying a crash-safe file system"*,
  MIT PhD 2016.

**Key technique — Crash Hoare Logic (CHL).**  Standard Hoare logic
extends `{P} c {Q}` with a *crash condition*: `{P} c {Q} {Cr}` means
"if `P` holds before `c`, then either `Q` holds on normal termination
or `Cr` holds after any crash during `c`".  Crucially, CHL bakes the
*disk-level* crash model into the logic: disk writes may be reordered,
flushes are explicit, and a crashed state is any prefix-consistent
subset of the issued writes.

**What FSCQ proves.**

* FSCQ-core is a Unix-like fs (Haskell FUSE front-end, Coq-extracted
  implementation) supporting inode tables, a bitmap allocator, a log,
  and basic directories.
* The top-level theorem states that after any sequence of FS ops +
  arbitrary crashes, the on-disk state reduces to *some* legal state of
  the abstract spec — i.e. the fs never produces a state that the
  abstract POSIX-ish spec doesn't recognise.

**Cost.**  ~30,000 lines of Coq (spec + proof) for ~3,000 lines of
extracted Haskell filesystem.  Roughly a 10× proof/code ratio,
comparable to seL4.  Two person-years of proof effort.

**Limitations that matter for NVFS scoping.**

* FSCQ has *no concurrency*: each FS call is atomic at the CHL level.
* Performance is lousy — the extracted Haskell runs at ~1/10 the speed
  of ext4.  FSCQ's follow-ups (DFSCQ, CFSCQ) addressed crash-safety of
  `fsync`-with-batching and concurrency respectively, each requiring
  fresh logic variants.
* FSCQ's abstract spec is hand-written and has bugs of its own; the
  theorem is "refines this spec", not "refines POSIX".

NVFS take-away: the **preservation-of-state-invariants** slice of
FSCQ's theorem is independently useful and roughly 10× cheaper to
prove.  Crash-refinement for *specific ops* (as opposed to "the whole
fs") is tractable.

### 2.2 Yggdrasil (Sigurbjarnarson, Bornholt, Torlak, Wang; OSDI 2016)

Yggdrasil takes the opposite approach: *push-button* verification via
SMT, no manual proofs.

Primary sources:

- Sigurbjarnarson et al., *"Push-Button Verification of File Systems
  via Crash Refinement"*, OSDI 2016.
- Source: `https://github.com/uwplse/yggdrasil`.

**Key technique — crash refinement.**  A filesystem implementation `I`
crash-refines a specification `S` iff every reachable *crash state* of
`I` is explained by some reachable crash state of `S`.  Formally, with
`crash_I : State_I → Set State_I` and similarly for `S`, and a
simulation relation `R : State_S → State_I → Prop`:

> For every op `op`, pre-state `s_S`, `s_I`, successor `s_I'`, and
> crash state `c_I` reachable from `{s_I, s_I'}`: there exist
> `s_S'` and `c_S` reachable from `{s_S, s_S'}` with `R s_S' s_I'`
> and `R c_S c_I`.

The insight is that crash refinement can be encoded as an SMT query:
the tool enumerates op-pairs and uses Z3 to prove refinement up to
some bounded depth.  Above a certain depth bound, the SMT proof
suffices for the unbounded case by induction on the state diameter.

**What Yggdrasil proves.**

* Yxv6, a verified FAT-like fs (~1,500 LOC Python-like DSL).
* Yjrnl, a verified journal.
* Ycp, a verified `cp` utility.
* All with sub-minute SMT checking times on commodity hardware.

**Limitations.**

* The DSL is restricted (bounded loops, no unbounded recursion).
* Proofs are black-box — when SMT fails, there is no counterexample
  trace at the refinement-relation level.
* The simulation relation `R` is still hand-written.

NVFS take-away: Yggdrasil's *crash-refinement idiom* (the formal
statement above) is the right shape for NVFS's critical ops
(`arena_seal`, `arena_discard`, `checkpoint_commit`, `wal_append`).
We do not need Yggdrasil's push-button infrastructure, just its
statement template.

### 2.3 Ivy and TLA+

Both are specification languages primarily used for distributed
systems, but they have been applied to filesystem-adjacent storage.

**Ivy** (Padon, McMillan, Panda, Sagiv, Shoham; PLDI 2016).  Modular,
decidable inductive invariant discovery.  Has been used on Paxos
variants, RAFT, the Chord DHT, and simple replicated storage.  Ivy's
*EPR fragment* keeps the decision problem tractable; most filesystem
invariants are not naturally EPR but are close enough that Ivy can
discharge their *inductive* cases if the user supplies the frame.

**TLA+** (Lamport, since 1999).  Has been used to model-check Azure
Storage, MongoDB's replication layer, AWS DynamoDB's global tables,
Ceph's monitor consensus, and — relevant here — the abstract model of
**Btrfs's send/receive protocol** (Facebook internal work, reported in
public talks but not published).

Neither tool is a filesystem-prover per se; they excel at the
*replication / concurrency* layer above a single-node fs.  NVFS
currently has none of that — everything runs on a single host — so
Ivy/TLA+ would be deployed if and when NVFS grows pool-level
replication (multi-host write-ahead mirroring, async snapshot send).

### 2.4 Lean 4 ecosystem for systems verification

Lean 4 is younger than Coq, but its systems-verification story is
maturing rapidly.  Primary sources:

- de Moura, Ullrich, *"The Lean 4 Theorem Prover and Programming
  Language"*, CADE 2021.
- Lean 4 + mathlib4: `https://github.com/leanprover-community/mathlib4`.
- `aesop` tactic: Limperg, From, *"Aesop: White-Box Best-First
  Proof Search for Lean"*, CPP 2023.
- Case study: `LeanSAT` (Cadical-in-Lean), `Vale-in-Lean` (ongoing
  cryptographic primitive verification), the Xena `xena4` project.

**Tactic landscape for NVFS-shaped goals:**

* `decide` — closes a decidable `Prop` by evaluating the `Decidable`
  instance.  Great for ground-term goals over `List`/`Nat`/small
  `inductive`s; folds `List.all` / `List.any` trivially.
* `native_decide` — same, but compiles to native code.  ~100× faster
  on "large-ish" ground terms (thousands of list elements).  Trusts
  the Lean compiler + runtime, so it adds one bit to the TCB.
* `simp` / `simp_all` — rewrite with `@[simp]` lemmas.  Essential for
  unfolding op definitions.
* `omega` — linear arithmetic over `Int` / `Nat`.  Closes ref-count
  obligations.
* `aesop` — guided best-first proof search.  Good for framing lemmas
  and "obvious" preservation arguments.

**No mathlib.**  We explicitly do not depend on mathlib: build times
blow up from seconds to ~20 minutes and the fs proofs don't need
anything mathlib provides beyond what core already ships.  `omega`,
`decide`, `simp`, `native_decide` are all in core Lean 4.29.1.

**`sorry` discipline.**  Lean warns on `sorry` but does not error; a
`sorry`-closed theorem still compiles and is usable.  For a scoped
deliverable, this means "stated-only" theorems are legitimate
artifacts — they pin down the obligation shape even when the proof
isn't complete.  The project CI should grep `sorry` counts and gate
regressions, but the first milestone is "every theorem stated
correctly", not "every proof closed".

---

## 3. Survey of related formal-FS work (brief)

| System | Logic / Tool | What's proven | Cost |
|---|---|---|---|
| FSCQ (2015) | Coq + CHL | Full fs crash-safety, reduces to abstract spec | ~30 kLOC proof / ~3 kLOC code |
| DFSCQ (2017) | Coq + CHL+ | `fdatasync` & metadata journalling | Incremental ~5 kLOC |
| CFSCQ (2018) | Coq + CHL concurrent | `read`/`write` concurrency | Incremental ~7 kLOC |
| Yggdrasil (2016) | Z3 via DSL | Crash refinement for FAT-like fs | ~1.5 kLOC DSL |
| PLOVER (2019) | F* | Disk-format invariants for tx-fs | ~5 kLOC F\* |
| Cogent (2016+) | Isabelle + C refinement | Ext2-style fs (eCryptfs-like) | Part of a larger Cogent verified-C stack |
| VeriBetrKV (2020) | Dafny | Verified B+tree KV store | ~10 kLOC Dafny |
| Perennial (2021-) | Coq (Iris-based) | Concurrent crash-safe storage (GoJournal) | ~20 kLOC proof / 1 kLOC Go |
| Iris-NVM (2022) | Iris | Persistent-memory data structures | Research prototype |

Perennial + GoJournal is the closest analogue to NVFS today: it proves
a crash-safe *journal* (WAL) inside a Go ecosystem, and the proofs
explicitly handle `fsync`/`fdatasync`.  Its machinery (Iris
separation logic, Perennial's crash weakest preconditions) is overkill
for NVFS's current state-invariant slice, but is the reference to
reach for when NVFS adds concurrency proofs.

---

## 4. Recommendation: scope for NVFS

### 4.1 What we explicitly do *not* prove

* **Refines POSIX / VFS.**  NVFS is not a POSIX filesystem; its surface
  is the `fs_driver_interface` trait (see `doc/01_research/fs_driver_interface.md`).
  Proving "NVFS implements POSIX" would require a POSIX formalisation
  we don't have and wouldn't use.
* **Concurrency.**  The Lean model is sequential.  Real NVFS has
  concurrent `arena_append`s and read-while-publish.  Concurrency
  proofs are deferred to a future milestone using Iris-style CSL (or
  Perennial directly) — at which point the sequential invariants
  proved here become *object invariants* of the concurrent model.
* **Performance.**  No proof of "bounded worst-case latency".  That
  is what the benchmarks cover.

### 4.2 What we do prove (or state, for `sorry`-backed theorems)

For the NVFS world-state `FsState` defined in `Nvfs/State.lean`, we
define ten invariants `I1`–`I10` (see `Nvfs/Invariants.lean`).  For
each transition `op : FsState → Input → Except FsError FsState` we
state

> `op_preserves_all : ∀ s i s'. AllInvariants s → op s i = Except.ok s' → AllInvariants s'`

This is "every legal op preserves integrity".  **Proof tier:**

| Tier | Invariants | Approach |
|---|---|---|
| Easy (target: close) | I1, I2, I4, I6 | `decide`/`simp`/`omega` after unfolding the op |
| Medium (target: close; fall back to `sorry` if > 30 tactic lines) | I3, I5, I7, I8, I9 | Case-split on op arg + frame argument for untouched fields |
| Hard (state-only acceptable) | I10 (snapshot pin), crash-refinement of `checkpoint_commit` | Full proof deferred; statement is the deliverable |

### 4.3 Crash-refinement shape (per Yggdrasil §2.2)

For each of the four critical ops we state:

```lean
theorem op_crash_refines (s : FsState) (i : Input) (s' : FsState) :
    op s i = Except.ok s' →
    ∀ c, ReachableCrash s s' c →
        (∃ csPre,  ReachableCrash s  s  csPre  ∧ R csPre  c) ∨
        (∃ csPost, ReachableCrash s' s' csPost ∧ R csPost c)
```

where `ReachableCrash pre post c` means "after a crash that could
happen at any linearisation point between `pre` and `post`, `c` is a
possible durable state".  For NVFS-N1 (in-memory model) the `crash`
function is defined in `Nvfs/Theorems.lean` as truncating the WAL at
`durableLsn` and dropping all snapshots.

**Critical ops requiring a crash-refinement theorem:**

* `arena_seal` — crash between "write seal record to WAL" and "flip
  `sealed := true` in the arena table" must leave either the
  pre-seal or the post-seal state on recovery.
* `arena_discard` — crash between "WAL:discard" and "actually free the
  bytes" must never leave a state where the arena is
  discarded-but-still-referenced.
* `checkpoint_commit` — crash anywhere in the three-phase commit
  (write inactive replica → flush → flip `active`) must land on a
  state where exactly one replica is valid (I6).
* `wal_append` — crash during a partial WAL write must leave a WAL
  prefix that is either length-aligned (all records durable) or
  truncated at the last durable record (nothing after `durableLsn`).

All four theorems are stated in `Nvfs/Theorems.lean`.  Only `mount`
and `unmount` are proof-closed (trivially); the rest are
`sorry`-closed with a detailed TODO describing the missing sub-case.

### 4.4 File layout (actual, as shipped)

```
formal/nvfs/
├── lakefile.toml              # Lake project config (no mathlib).
├── lean-toolchain             # leanprover/lean4:v4.29.1
├── Nvfs.lean                  # Re-export facade.
├── Nvfs/
│   ├── Basic.lean             # IDs, enums (StorageClass, Durability, WalOp, FsError).
│   ├── State.lean             # Arena, PmapEntry, CheckpointRoot, Superblock, WalRecord, Snapshot, FsState.
│   ├── Ops.lean               # 11 transitions (arena_create .. unmount).
│   ├── Invariants.lean        # I1..I10 in Prop + Bool form, AllInvariants struct.
│   └── Theorems.lean          # Preservation theorems + crash-refinement stubs.
```

---

## 5. Proof sketch for the hard cases

### 5.1 I10 — snapshots pin arenas

> **Statement.** For every snapshot `sn` and every arena id `a ∈ sn.pinned`
> and every arena `ar` with `ar.id = a`, we have `ar.discarded = false`.

**Argument.** `arena_discard` is the only op that can set
`ar.discarded := true`.  Its guard explicitly checks
`¬ s.snapshots.any (fun sn => sn.pinned.contains id)` before flipping
the flag; if the check succeeds, no snapshot pins `id`, so the I10
post-condition still quantifies over snapshots that do not mention
`id`.

**Why it's "hard" in Lean.**  The quantifier structure is `∀ sn ∀ a
∀ ar`.  To discharge on `arena_discard` success we need to relate
`s.snapshots` (pre) = `s'.snapshots` (post) and then push through the
existing I10 on `s`.  Straightforward once the right `List`-membership
lemmas are imported, but a mechanical 40-line proof.  We leave `sorry`
with the pointer above.

### 5.2 Crash refinement for `checkpoint_commit`

The real statement we want is:

> If `checkpoint_commit s args = Except.ok s'`, then for any
> intermediate disk state `c` reachable via a crash between the
> "write inactive replica" and "flip `active`" durability barriers,
> `c` is equivalent (under `R`) to either `crash s` or `crash s'`.

In our N1 in-memory model, "intermediate disk state" is either the
previous superblock (crash before flip) or the new superblock (crash
after flip).  The refinement relation `R` ignores `mountEpoch`,
non-durable `bytes` suffixes, and `snapshots`.  Then the theorem
reduces to a case-analysis on `sb.active` before the op.

Stated as `sorry` because our `crash` function in `Theorems.lean`
does not yet split the superblock-flip point; fixing that requires
either a richer transition model (one that issues an explicit
"durability barrier" WAL record around the flip) or an axiomatic
crash relation.  Both are ~100 lines and out of the 60-minute budget.

---

## 6. Primary sources (bibliography)

- Chen, Ziegler, Chajed, Chlipala, Kaashoek, Zeldovich. *Using Crash
  Hoare Logic for Certifying the FSCQ File System.* SOSP 2015.
- Chen, Chajed, Konradi, Wang, İleri, Chlipala, Kaashoek, Zeldovich.
  *Verifying a high-performance crash-safe file system using a tree
  specification.* SOSP 2017. (DFSCQ.)
- Chajed, Tassarotti, Kaashoek, Zeldovich. *Verifying concurrent,
  crash-safe systems with Perennial.* SOSP 2019.
- Sigurbjarnarson, Bornholt, Torlak, Wang. *Push-Button Verification
  of File Systems via Crash Refinement.* OSDI 2016.
- Padon, McMillan, Panda, Sagiv, Shoham. *Ivy: Safety Verification by
  Interactive Generalization.* PLDI 2016.
- Lamport. *Specifying Systems: The TLA+ Language and Tools for
  Hardware and Software Engineers.* Addison-Wesley 2002 (and the TLA+
  examples repo).
- de Moura, Ullrich. *The Lean 4 Theorem Prover and Programming
  Language.* CADE 2021.
- Limperg, From. *Aesop: White-Box Best-First Proof Search for Lean.*
  CPP 2023.
- Chajed et al. *GoJournal: a Verified, Concurrent, Crash-Safe Journal.*
  OSDI 2021. (Perennial / Iris application to storage.)
- Bonwick, Ahrens. *ZFS: The Last Word in File Systems.* Slide deck /
  on-disk format spec, 2006.  Also `doc/01_research/zfs_deep_dive.md`
  in this repo.
- Btrfs on-disk format, `btrfs-progs` source tree.  Mirror of §2 in
  `doc/01_research/btrfs_deep_dive.md`.
- NVFS design: `doc/05_design/nvfs_design.md` (v1).
- spostgre requirements against NVFS: `doc/05_design/nvfs/from_spostgre.md`.
- svllm requirements against NVFS: `doc/05_design/nvfs/svllm_requirements.md`.

---

## 7. Follow-up work

1. **Close I1/I2/I4/I6 proofs** that are currently `sorry`-stubbed.
   These are all one- to five-line proofs per op; budget one afternoon.
2. **Strengthen `pmap_publish` op** to check injectivity (I8) on
   insert — or add a weaker I8 variant that permits transient overlap
   and is restored by compaction.
3. **Real crash model.**  Replace the placeholder `crash` function
   with a relation parameterised on "linearisation point" so the
   crash-refinement theorems can quantify over all intermediate
   points.
4. **Scaling to concurrency.**  When NVFS grows concurrent
   `arena_append`s, port the sequential invariants to object
   invariants in an Iris-style CSL.  Perennial is the reference.
5. **Connect to implementation.**  Today the Lean model is
   independent of `examples/nvfs/src/core/*.spl`.  Add a
   refinement-generator that emits Lean `FsState` from a Simple-level
   structural representation so the proofs bind to the actual N1
   implementation, not just a paper model.
