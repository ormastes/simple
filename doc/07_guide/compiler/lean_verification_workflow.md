# Lean Verification Workflow Guide

**Status:** Active
**Date:** 2026-04-04
**Contract:** [doc/04_architecture/infra/misc/lean_verification_contract.md](../04_architecture/lean_verification_contract.md)

This guide describes how to use the Simple compiler's Lean 4 formal verification workflow. The workflow translates annotated Simple source code into Lean 4 proof obligations, checks them with the Lean toolchain, caches results incrementally, and reports verification status at multiple levels.

---

## Quick Start

```bash
# 1. Install Lean 4 (stable channel)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/main/elan-init.sh | sh

# 2. Check toolchain readiness
simple verify status

# 3. Generate Lean proof obligations from your annotated code
simple gen-lean write

# 4. Verify all generated proofs
simple verify check

# 5. View the verification report
simple verify list
```

### Minimal Verified Function

```simple
@verify
fn factorial(n: i64) -> i64:
    in: n >= 0
    out(ret): ret > 0
    decreases: n
    if n == 0:
        1
    else:
        n * factorial(n - 1)
```

Running `simple gen-lean write` produces a Lean 4 file with:
- A `theorem factorial_pre_0` for the precondition `n >= 0`
- A `theorem factorial_post_0` for the postcondition `ret > 0`
- A `decreases` annotation for termination

Running `simple verify check` invokes Lean/Lake to check these theorems. Unproven obligations use `sorry` and are reported as **admitted** (proof debt).

---

## Supported Verification Features

The verification workflow supports a bounded subset of formal verification. All features below are tested and documented. Deferred features are listed in [Known Limitations](#known-limitations).

Maintain generated Lean separately from handwritten proof lemmas. Regeneration
may replace generated declarations, but durable proof files should import those
declarations and prove small named invariants such as resource-capacity,
capability-depth, channel-backpressure, and DRF/race lemmas. This keeps later
Lean or BYL backend regeneration from breaking manually added proof intent.

### @verify Attribute

Marks a function for formal verification. The compiler generates Lean proof obligations from the function's contracts.

```simple
@verify
fn abs(x: i64) -> i64:
    out(ret): ret >= 0
    if x >= 0: x else: -x
```

**Classification:** stable
**Restriction:** Verified functions must be pure -- no IO, Net, Fs, or async effects (rule V-EFFECT). No `@unsafe` operations (rule V-UNSAFE). No reflection (rule V-REFLECT).

### Contracts (in:/out:/invariant:/decreases:)

Contracts specify preconditions, postconditions, invariants, and termination measures.

| Contract | Syntax | Purpose |
|----------|--------|---------|
| Precondition | `in: expr` | Must hold on function entry |
| Postcondition | `out(ret): expr` | Must hold on function exit; `ret` binds the return value |
| Error postcondition | `out_err(err): expr` | Must hold when function returns an error |
| Invariant | `invariant: expr` | Must hold for class/struct instances |
| Decreases | `decreases: expr` | Termination measure for recursive functions |
| Old expression | `old(expr)` | Refers to pre-call value in postconditions |

**Example with all contract types:**

```simple
class Counter:
    count: i64
    invariant: self.count >= 0

@verify
fn increment(c: Counter) -> Counter:
    in: c.count < 1000
    out(ret): ret.count == old(c.count) + 1
    Counter(count: c.count + 1)
```

**Qualifiers:**
- `out_err:` supports limited expression forms
- `old()` supports simple field access only (not arbitrary expressions)
- `invariant:` applies to class invariants only
- `decreases:` supports a single measure expression

### Ghost and Spec-Only Code (@ghost)

Ghost functions exist only for specification purposes. They are erased at the MIR level before codegen -- they produce no runtime code. Ghost functions must be pure and side-effect-free.

```simple
@ghost
fn sorted(xs: [i64]) -> bool:
    for i in 0..xs.len() - 1:
        if xs[i] > xs[i + 1]:
            return false
    true

@verify
fn insert_sorted(xs: [i64], x: i64) -> [i64]:
    in: sorted(xs)
    out(ret): sorted(ret)
    # ... implementation ...
```

**Classification:** stable
**Invariant:** Ghost params and locals are removed from MIR before codegen. They appear only in generated Lean modules.

### Trusted Code (@trusted)

Marks a function as axiomatically trusted. No proof obligations are generated -- the function's contracts are assumed to hold. This is **proof debt**, not verification.

```simple
@trusted
fn read_file(path: text) -> text:
    in: path.len() > 0
    out(ret): ret.len() >= 0
    # FFI call to OS -- cannot be verified
    rt_file_read_text(path)
```

**Classification:** stable
**Rule V-TRUSTED:** Trusted boundary functions must have contracts. A `@trusted` function without contracts triggers a verification warning.
**Reports always show trusted count prominently.** Trusted is never displayed as "verified."

### Embedded Lean Blocks (lean{})

Embed raw Lean 4 code directly in Simple source. The content is included verbatim in the generated Lean module. Imports within `lean{}` blocks are deduplicated with the generator's default imports.

```simple
lean {
    import Mathlib.Tactic

    theorem helper_lemma (n : Nat) : n + 0 = n := by simp
}
```

**Classification:** supported_with_qualifiers
**Restrictions:**
- Module-level placement only for v1 (not inside function bodies)
- Namespace collision detection: if a `lean{}` block defines a theorem with the same name as a generated obligation, a collision warning is emitted
- Import lines inside `lean{}` blocks are stripped from the body and merged into the top-level import section

### External Proof References (proof uses:)

Reference a theorem defined in an external Lean file under `src/verification/proofs/`.

```simple
@verify
fn gcd(a: i64, b: i64) -> i64:
    in: a > 0
    in: b > 0
    out(ret): ret > 0
    proof uses: gcd_positive_theorem
    # ...
```

The compiler resolves the reference by searching for `gcd_positive_theorem` in external Lean modules and imports it into the generated proof module.

**Classification:** supported_with_qualifiers
**Restriction:** Theorem matching is manual -- the theorem name must exactly match what is defined in the external file.

---

## Verification Commands

All commands use the `simple` binary. No subprocess calls are needed.

### Generation Commands

| Command | Purpose |
|---------|---------|
| `simple gen-lean generate` | Output generated Lean code to stdout (does not write files) |
| `simple gen-lean write` | Write generated Lean files to `src/verification/` directory |
| `simple gen-lean compare` | Diff generated vs existing Lean files; check completeness |
| `simple gen-lean verify` | Run Lean/Lake on generated files and fail on errors/sorry |

### Verification Commands

| Command | Purpose |
|---------|---------|
| `simple verify status` | Show Lean toolchain availability and verification artifact inventory |
| `simple verify check` | Verify all proof obligations using Lean/Lake |
| `simple verify list` | List all verification artifacts and their current state |

### Typical Workflow

```bash
# After modifying @verify functions:
simple gen-lean write        # Regenerate Lean files
simple verify check          # Run proofs
simple verify list           # Review results
```

### Maintainable Generated Proof Surfaces

Generated verification code must keep tool-owned and human-owned files
separate. Regeneration may replace generated Lean modules, generated BYL
proof-model files, and their manifests. It must not overwrite the manual
constraint/proof layer.

Recommended layout:

| File | Owner | Purpose |
|------|-------|---------|
| `Generated.lean` | generator | Stable base definitions emitted from Simple/MIR/product metadata |
| `Constraints.lean` | manual | Added constraints, theorems, and proof obligations over generated names |
| `*.byl` | generator | Compact proof-model IR for tools that do not need full Lean syntax |
| `GENERATED_CONTRACT.md` | generator + reviewer | Stable exported names that regeneration must preserve |

BYL is not a replacement for Lean. Treat BYL as a generated proof-model
interchange format and Lean as the checked proof surface. If regeneration
renames a definition used by `Constraints.lean`, update the generated contract
and the manual proof layer in the same change, then run Lake. When formal
evidence is referenced from a SPipe scenario or hardening report, record the
lane-specific `lake build`, `simple gen-lean verify`, or `simple verify check`
command beside the evidence so the next regeneration can rerun the exact gate
without weakening manual proofs.
Do not add proof intent directly to generated BYL output. Put added invariants
and theorem obligations in the manual Lean layer, then keep the BYL generator
focused on stable, compact facts consumed by that layer. If BYL grows a new
export needed by a manual theorem, update `GENERATED_CONTRACT.md` and the manual
proof in the same change.

Regeneration must be append-safe for manual proof work:
- generated Lean/BYL files may be replaced by the backend;
- manual theorem files should only import generated names and stay stable;
- generated manifests must list the exported names consumed by manual proofs;
- SPipe evidence should cite both the generated artifact and the stable manual
  theorem entry point checked after regeneration.
- generated-only citations are insufficient for SPipe or hardening-report
  evidence when a manual theorem/constraint layer exists.
- added proof intent belongs in the manual theorem/constraint file, not in a
  generated Lean or BYL file, unless the generator contract is updated in the
  same change.
- SPipe and hardening-report rows must name the post-regeneration proof gate
  (`lake build`, `simple gen-lean verify`, or `simple verify check`) next to the
  generated artifact and manual theorem file.

For RISC-V product work, do not collapse the two proof layers into one status.
Generated BYL can make proof-model regeneration cheaper, but mission-critical
claims still need the hardware-side RVFI/SymbiYosys gate when RTL sidecars are
in scope and the Lean/manual theorem gate when resource or concurrency
properties are modeled above RTL. The critical SimpleOS gate pins named
resource-capacity, closed-channel drain, DRF race/synchronized-safe, and
memory-capability uniqueness theorems so regeneration cannot silently drop
manual proof intent.
When the claim is about agent resources, scheduler fairness, starvation,
channel backpressure, lock ordering, or race freedom, the evidence row must
name the model scope and exact checked gate. A generated Lean or BYL artifact
is only the regenerated input surface; the claim is not formal evidence until
the durable theorem file and its `lake build`, `simple gen-lean verify`, or
wrapper gate pass after regeneration.

### RISC-V Dual-Track Formal Evidence

RISC-V lanes that span generated RTL and higher-level Lean or BYL proof models
must keep the evidence split by layer. RTL readiness or proof artifacts belong
to the RVFI/riscv-formal/SymbiYosys lane; Lean remains the checked theorem
surface for Simple-level properties; BYL is generated proof-model interchange
that can make regeneration cheaper but does not replace the checked proof
command.

Use the aggregate gate when a change crosses those boundaries:

```bash
sh scripts/check/check-riscv-formal-dual-track.shs
```

That wrapper is the citation to use in SPipe docs and hardening reports when
both generated sidecars and manual theorem constraints must survive
regeneration.

For SimpleOS mission-critical claims, the dual-track gate is still not a
release gate by itself. Cite `sh scripts/check/check-riscv-rtl-sby-proof.shs`
for the strict RVFI/SymbiYosys proof lane and
`sh scripts/check/check-simpleos-mission-critical-release.shs` for the final
release decision, which also requires `release_blockers=none`. If `sby`,
`yosys`, or an SMT solver is missing, report the result as blocked readiness
evidence, not as a proof pass.

---

## Verification States

Every proof unit (file-level for v1) has exactly one of six states:

| State | Display | Meaning |
|-------|---------|---------|
| `verified` | Verified | All obligations checked by Lean with no admits or trust |
| `failed` | FAILED | Proof check ran and at least one obligation failed |
| `admitted` | Admitted (sorry) | Obligations remain via `sorry`/`admit` -- **proof debt** |
| `trusted` | Trusted (assume) | Obligations bypassed via `@trusted`/`assume` -- **proof debt** |
| `stale` | Stale | Cached result exists but inputs have changed since last check |
| `not_checked` | Not Checked | Lean artifacts may exist but proof check has not been run |

### State Transitions

```
not_checked  -->  verified | failed | admitted | trusted   (after proof check)
verified     -->  stale                                    (on source/dep change)
failed       -->  stale                                    (on source/dep change)
admitted     -->  stale                                    (on source/dep change)
trusted      -->  stale                                    (on source/dep change)
stale        -->  verified | failed | admitted | trusted   (after re-check)
any state    -->  not_checked                              (on cache clear)
```

### Aggregation

When rolling up states from file level to project level, the most severe state wins:

`failed` > `admitted` > `trusted` > `stale` > `not_checked` > `verified`

A project reports `verified` only when **every** proof unit is individually `verified`.

### Admitted and Trusted are Proof Debt

**Admitted** means the obligation contains `sorry` or `admit` -- Lean accepts the file but the theorem is not actually proven. This is proof debt that must be resolved before claiming full verification.

**Trusted** means the obligation is axiomatically assumed via `@trusted` or `assume`. The function's contracts are not checked by Lean. This is appropriate for FFI boundaries but is still proof debt.

Reports always show admitted and trusted counts prominently. Neither state is ever rendered as "verified" or displayed with success styling.

---

## Cache and Incremental Verification

### Cache Location

Verification results are cached in `build/verification-cache/`. This directory is git-ignored.

### Fingerprint Inputs

A cache entry's fingerprint is computed from:

1. **Source file content** -- the `.spl` file with `@verify` annotations
2. **Generated Lean content** -- the `.lean` file produced by `gen-lean write`
3. **Dependency file hashes** -- imported proof module paths
4. **Lean toolchain version** -- from `lean-toolchain` file
5. **Semantic dependency shape** -- public ABI, accessor-forwarding, and field-wrapper dependencies that can change a dependent module's meaning

Any change in these inputs marks the proof unit as `stale`.

### Invalidation Rules

- Editing a source file invalidates its own cache entry
- Editing an external proof module invalidates all proof units that depend on it
- Changing a wrapped field, forwarded getter/setter, or public ABI member invalidates dependent units that mention that semantic edge
- Changing the Lean toolchain version invalidates all cache entries
- Running `simple verify check` after invalidation re-checks affected units
- Stale entries are never returned from cache lookups (safety invariant)

Field-wrapper invalidation is fail-closed. If module `A` refers to `B` through a
forwarded field or generated accessor and `B` wraps, unwraps, renames, or
changes that field's accessor shape, `A` must miss the verification cache. The
same semantic key is mirrored into the interpreter incremental path, SMF loader
cache, and JIT instantiator cache so stale executable artifacts are not reused
after meaning-changing accessor changes.

### Cache Format

Each entry is stored as an SDN file (one per source file) containing:
- fingerprint hash
- verification state
- per-theorem results (proven/failed/admitted)
- ISO-8601 timestamp
- Lean version
- source file path

### Cache Statistics

After running `simple verify check`, cache performance is reported:
- Total entries, hits, misses, stale count, hit rate percentage

---

## Reporting and Diagnostics

Verification reports are available at four levels of detail:

| Level | Shows |
|-------|-------|
| **Project** | One-line summary: "3 verified, 1 failed, 2 admitted" |
| **File** | Per-file state with obligation counts and debt markers |
| **Symbol** | Per-function/type verification state |
| **Theorem** | Individual theorem detail with source origin and Lean file path |

### Report Features

- **Debt visibility:** Admitted and trusted counts are always shown prominently with `[N sorry]` and `[N assume]` markers
- **Error separation:** Environment errors (missing Lean, wrong version) are reported separately from proof failures
- **Machine-readable output:** Reports can be rendered in SDN format for tool integration
- **Source tracing:** Failed theorems include source file and line number

### Environment vs Proof Errors

The reporting system distinguishes between:
- **Environment errors:** Lean not found, version mismatch, Lake dependency failures. These indicate toolchain setup problems, not proof failures.
- **Proof errors:** Theorem check failures, `sorry` obligations, type errors in generated Lean. These indicate actual verification gaps.

---

## Generated-Mirror / Manual-Proof Split

A proof file mixes two kinds of content: **definitions** that mirror the Simple code (constants, geometry, the state/selection model) and **theorems** that prove properties about them. The definitions are the only part *coupled to the implementation* — so they must be cheap to re-derive when the code changes, without disturbing the hand-written proofs. Keep them separated.

There are two supported shapes; pick by how the file is checked:

**1. In-file marked sections** — for standalone proofs checked by raw `lean <file>`.

```lean
-- BEGIN gen lean: mirror of fw/ftl_band.spl (constants + alloc geometry).
--   Regenerate when the Simple code changes; defs only, NO proofs here.
def ppn (b wp : Int) : Int := b * 64 + wp
def GC_RESERVE : Int := 2
-- END gen lean

-- MANUAL PROOFS (hand-written; stable across a re-mirror of the gen section above).
theorem alloc_in_range ... := by unfold ppn; omega
```

Raw `lean <file>` does **not** resolve sibling-source `import`s (it only finds `.olean` on `LEAN_PATH` or a Lake project), so a standalone proof keeps both sections in one file. The marked `gen lean` block is what makes re-transcription a localized edit. This is the model used by `examples/09_embedded/simpleos_nvme_fw/{fw,emu}/proofs/*.lean`.

**2. Two files in a Lake project** — for proofs built with `lake build` under `src/verification/<project>/`.

```lean
-- <Name>/Basic.lean  — definitions (the generated mirror)
namespace <Name>.Basic
def ...
-- <Name>/Theorems.lean — proofs
import <Name>.Basic
open <Name>.Basic
theorem ...
```

`import`/`open` work here because Lake puts the package modules on the search path. Used by `actor_channel`, `fat32`, `gc_boundary`, `nvfs`, etc.

### Re-gen discipline (correspondence rule)

On a Simple-code change that touches a verified/mirrored path:

1. Re-transcribe **only** the `gen lean` section (or `Basic.lean`) so the defs match the new code.
2. Re-check: `lean <file>` for standalone proofs, `lake build` for Lake projects, or `simple gen-lean compare` for the gen-lean regeneration tree.
3. If a def *signature* — or a constant that also appears in a theorem statement (e.g. a geometry bound like `wp < 64`) — changed, the manual proofs need follow-up; a pure def-body change usually leaves them green. Keep def names and namespaces **stable** so external proofs referencing them do not silently break.

### What `gen-lean` does and does not generate

`simple gen-lean generate|write|compare|verify` operate on a **fixed inventory** of `src/.../verification/regenerate/*.spl` modules — they do **not** scan arbitrary `@verify` user files and cannot emit algorithm Lean for an arbitrary `.spl` (only `gen-lean memory-safety --file <p>` consumes a user file, and only for memory-safety obligations). So for code outside that inventory — the NVMe firmware/emulator, for example — the mirror defs are **hand-transcribed** under the marked `gen lean` section, not machine-generated. `gen-lean write --force` overwrites whole files with **no** manual-edit preservation, so never hand-edit a file the regeneration tree owns; edit its source module instead.

> The `bin/simple gen-lean` CLI is currently broken (the wrapper re-spawns itself and infinitely recurses; the Rust codegen is unreachable through the CLI) — see `doc/08_tracking/bug/gen_lean_cli_infinite_recursion_2026-06-30.md`. Until that is fixed, the regeneration tree is reachable only by internal callers, and the hand-transcribed in-file split above is the working path for example/firmware proofs.

---

## Known Limitations

### Deferred (Out of Scope for This Milestone)

| Feature | Reason |
|---------|--------|
| Loop invariants | Requires bounded loop analysis |
| Refinement types | Separate gated subset, too broad for this milestone |
| Automatic proof synthesis | Research-grade, not productizable yet |
| Full dependent typing | Language-level change beyond the verification subset |
| Replacing SPipe with proofs | Different concern (testing vs verification) |

### Current Restrictions

- **File-level granularity:** Proof units are tracked per source file, not per function. Symbol-level granularity is planned for a follow-on milestone.
- **Pure functions only:** `@verify` functions must be pure. Functions with IO, Net, Fs, or async effects cannot be verified (use `@trusted` for FFI boundaries).
- **Single decreases measure:** Only one expression is supported per `decreases:` clause.
- **old() expressions:** Limited to simple field access (`old(self.x)`), not arbitrary nested expressions.
- **lean{} blocks:** Module-level placement only. Cannot embed Lean code inside function bodies.
- **Proof references:** Manual theorem name matching. No automatic resolution or fuzzy matching.
- **Error postconditions:** Limited expression forms supported.

---

## Examples

### Verified Arithmetic

```simple
@verify
fn add_positive(a: i64, b: i64) -> i64:
    in: a > 0
    in: b > 0
    out(ret): ret > a
    out(ret): ret > b
    a + b
```

### Ghost Specification with Trusted Boundary

```simple
@ghost
fn is_valid_path(path: text) -> bool:
    path.len() > 0 and not path.contains("..")

@trusted
fn safe_read(path: text) -> text:
    in: is_valid_path(path)
    out(ret): ret.len() >= 0
    rt_file_read_text(path)
```

### Embedded Lean Proof

```simple
@verify
fn double(n: i64) -> i64:
    in: n >= 0
    out(ret): ret == 2 * n
    n + n

lean {
    theorem double_correct (n : Int) (h : n >= 0) : n + n = 2 * n := by ring
}
```

### Class with Invariant

```simple
class BoundedBuffer:
    items: [i64]
    capacity: i64
    invariant: self.items.len() <= self.capacity
    invariant: self.capacity > 0

@verify
fn push(buf: BoundedBuffer, item: i64) -> BoundedBuffer:
    in: buf.items.len() < buf.capacity
    out(ret): ret.items.len() == old(buf.items.len()) + 1
    BoundedBuffer(items: buf.items.push(item), capacity: buf.capacity)
```

---

## Required Toolchain

- **Lean 4:** Version pinned in `lean-toolchain` (currently `leanprover/lean4:stable`)
- **Lake:** Installed automatically with Lean; must be compatible with the pinned Lean version
- **Mathlib:** Optional dependency, version pinned in `lakefile.lean` when used

Install Lean 4 via [elan](https://github.com/leanprover/elan):
```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/main/elan-init.sh | sh
```

Check readiness:
```bash
simple verify status
```

The status command reports Lean availability, version match against `lean-toolchain`, and Lake availability.

---

## Reference

- **Contract:** [doc/04_architecture/infra/misc/lean_verification_contract.md](../04_architecture/lean_verification_contract.md) -- authoritative feature matrix and state model
- **Support matrix:** Section 5 of the contract document
- **Verification checker rules:** V-UNSAFE, V-EFFECT, V-REFLECT, V-GHOST, V-TRUSTED, V-PARTIAL
- **Cache directory:** `build/verification-cache/`
- **Generated Lean output:** `src/verification/` subdirectories
