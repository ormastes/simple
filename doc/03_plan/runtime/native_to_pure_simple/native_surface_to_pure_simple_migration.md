# Migrating Native Surfaces to Pure Simple — Release-by-Release

**Status:** Plan (lane C, 2026-09-06).
**Instrument:** `src/lib/nogc_sync_mut/dual_fs/__init__.spl` (switchable wrapper +
differential effect comparison), `std.common.spec.dual_run` `FsEffect` /
`dual_check_fs_effect`, acceptance spec
`test/01_unit/lib/dual_fs/dual_fs_effect_compare_spec.spl`, gate
`scripts/check/check-dual-fs-effect-compare.shs`.
**Prior art this extends:** `scripts/check/check-dual-run-shadow.shs` (value
comparison) and `doc/07_guide/os/hal/pure_simple_hal.md` §2 (twin discipline).

---

## 0. Why a plan, and why it starts with an instrument

Two incidents motivate this whole lane, and both are *silent*:

| Incident | Shape | Why every existing check missed it |
|---|---|---|
| `std.file_system.file_write_text` is a mock | validates args, evaluates `true`, performs **no I/O** | the return value is CORRECT; only the world is wrong |
| unregistered extern returns nil (`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`) | missing runtime backing yields `nil`, not a fault | absence of a symbol is indistinguishable from a `nil` result |

**A third was found by this harness while building it**, which is the best
available evidence that the instrument earns its place:
`doc/08_tracking/bug/io_runtime_file_write_resolves_to_retryless_twin_2026-09-06.md`.
`use std.io_runtime.{file_write}` resolves to a **same-signature definition
with no parent-directory retry** (`src/lib/nogc_sync_mut/database/atomic.spl:39`
or `src/lib/nogc_async_mut/io/mod_stub.spl:29`), so writing into a missing
directory returns `false` and creates nothing — while the definition the
`use` names carries explicit repair logic for exactly that case. Measured:

```
std.io_runtime.file_write -> false exists=false      # retry never ran
captured-retry version:
  dir_create_all(build/probe7_y)=true retry=true
captured-retry -> true exists=true                   # identical logic, local fn
```

The existing interpreter warning for this class fires only when the colliding
signatures *differ*; identical signatures — the more dangerous case — are
silent.

Reproduced on this tree, unmodified:

```
$ bin/simple run build/scratch/probe3.spl     # std.file_system.file_write_text
returned=true exists=false size=-1
```

The root cause is structural and is **not** fixed by this plan: the function
registry is keyed on **name alone**. Measured 2026-09-06 under `src/lib`:

* **7** files define `file_write_text`
* **10** files define `file_write`
* **2,182** distinct `rt_*` externs are declared, **48** of them `rt_file_*`

Three `file_write_text` definitions differ in *behaviour*, not merely in
signature:

| Definition | Behaviour |
|---|---|
| `src/lib/nogc_sync_mut/file_system/file_ops.spl:60` | returns `true`, writes nothing |
| `src/lib/nogc_async_mut/file_system/file_ops.spl:59` | identical mock |
| `src/lib/gc_async_mut/file_system/file_ops.spl:18` | delegates to `std.io_runtime.file_write` — really writes |

So the *first* thing to ship is not a migration. It is an instrument that makes
a divergence loud, because a migration performed without one just moves the
silence around. Every release below is gated on evidence that instrument
produces.

## 1. How the instrument relates to what already exists

`std.common.spec.dual_run` and `check-dual-run-shadow.shs` compare **return
values** (`dual_check_f64` / `_text` / `_i64` / `_bool` / `_bytes`) across 41
annotated pairs. That vocabulary is correct for numeric and string twins and
useless for I/O: on the mock above, `dual_check_bool("write", true, true)`
reports **agreement**.

This lane adds the missing axis rather than a second framework:

* `FsEffect { returned, err, exists, size, digest, mode }` and
  `dual_check_fs_effect` live **in `std.common.spec.dual_run` itself**, reuse
  `DualVerdict`, and aggregate through the existing `dual_summarize` /
  `dual_verdict_report`. One verdict vocabulary, one summary shape.
* The pair is annotated `# @dual_pair: ... mode=effect-compare` and writes no
  ledger rows, so `check-dual-run-shadow.shs` reads it through the spec's
  `Results:` line exactly as it reads the `mode=value-legacy` tranches. No
  half-integration, no unparsable ledger row.
* Against `pure_simple_hal.md` §2, this is the same twin discipline applied to
  a surface whose equivalence is only observable as an **effect**. Rungs 1–4 of
  §3 (typed register views → intrinsics → asm last) are the *register* analogue;
  this is the *filesystem* analogue.

**Comparison design, and how it catches a write that returns success without
writing.** The probe reads the world through raw runtime externs
(`rt_file_exists`, `rt_file_size`, `rt_file_read_text`, `rt_file_mode`) and
**never through either implementation under test** — a mocked reader would
otherwise corroborate a mocked writer. Both sides write to distinct scrubbed
sandbox paths; effects are compared field-wise and the verdict names the fields:

```
DIVERGE file_write_text [diverged: exists=false/true size=-1/13
  digest=/fnv1a:3518544681 mode=-1/436 ]:
  simple=returned=true err='' exists=false size=-1 digest= mode=-1
  oracle=returned=true err='' exists=true  size=13 digest=fnv1a:3518544681 mode=436
```

`returned` is **absent from the diverged list** — both sides returned `true`.
That absence *is* the incident. `exists`, `size`, `digest` and `mode` all
diverge, so the report says "the write returned true and created no file"
rather than "a pair diverged". Two further details are load-bearing, not
polish:

* **absent is `size=-1`, an existing empty file is `size=0`.** If both probed
  as `0`, a writer that creates nothing and a writer that truncates to zero
  would compare equal and the harness would be blind again.
* **paths are scrubbed before each run**, so a leftover file from a previous
  run cannot make a non-writing side look like a writing one.

**A divergence FAILS; it never warns.** `dual_check_fs_effect` sets
`agree: false`, `dual_summarize` counts it, the spec asserts
`summary.divergent == 0`, and the gate's verdict is `FAIL` with exit 1.

## 2. The switch

```
SIMPLE_FS_PROVIDER = native | pure | diff        # unset => native
```

`native` is today's behaviour **by construction**: it calls
`std.io_runtime.file_write` / `read_file_text`, the exact path existing callers
already take. Unset therefore changes nothing for anyone. Anything
unrecognised — empty, misspelled — also resolves to `native`; a typo silently
selecting an experimental provider would be a worse failure than a typo being
ignored. `rt_env_get` is read with `?? ""` because the interpreter can hand
back nil for an unset variable and an unguarded `.len()` on that is a
documented crash (`src/lib/gc_async_mut/gpu/engine2d/engine.spl:1175`).

`diff` is deliberately **not** reachable from `dual_fs_write_text`: comparing
in place would need two distinct paths to write to, and a wrapper that
silently redirected a caller's path would be its own hazard. Differential
coverage is requested explicitly via `dual_fs_write_text_diff(name, path_a,
path_b, content, write_a, write_b)`.

## 3. Classification of the 48 `rt_file_*` surfaces

Migratability is a property of *where the syscall is*, not of how much code
there is. Three classes:

| Class | Meaning | Count | Migratable to pure Simple? |
|---|---|---|---|
| **A — composition** | orchestration, policy, ordering and error mapping ABOVE a leaf; performs no syscall of its own | ~18 | **Yes, now.** This is where all three `file_write_text` variants actually disagree. |
| **B — derived** | a leaf plus a pure transform (hash, text decode, line split, path normalise) | ~12 | **Partly.** The transform migrates; the leaf does not. |
| **C — syscall leaf** | the operation IS the syscall (`open`, `close`, `read`, `write`, `stat`, `mode`, `remove`, `rename`, `lock`, `fsync`, `mmap`, `canonicalize`) | ~18 | **No — see §6.** |

## 4. Release sequence

Each release ships something independently verifiable. There is no big-bang
step, and no release depends on a later one being finished.

### R1 — the instrument (this change)

* **Ships:** `std.dual_fs` wrapper (`native`/`pure` switch, `native` default),
  `FsEffect` + `dual_check_fs_effect` in `std.common.spec.dual_run`, acceptance
  spec (6 cases), gate `check-dual-fs-effect-compare.shs` wired into the
  required CI job `Code Idiom & Structural Ratchet Gates`.
* **Twin status:** `fs_write_text_native` vs `fs_write_text_pure` **agree** on
  effects across 5 content shapes including empty and multi-byte
  (`OK native_vs_pure: ... size=10 digest=fnv1a:1402669177 mode=436` both sides),
  **when the parent directory exists**. When it does not, they diverge and the
  *pure* side is the correct one — `fs_write_text_pure` performs the retry that
  the native path's resolved definition does not (bug filed, §0).
  `std.dual_fs.ensure_dir` therefore creates the sandbox explicitly: a fixture
  that leaned on a writer's own retry would be measuring its own setup.
* **Risk:** none to existing callers — the switch is unset, the default path is
  literally `std.io_runtime.file_write`, and the spec asserts
  `fs_provider() == FS_PROVIDER_NATIVE` under CI conditions.
* **Evidence to flip a default:** n/a — R1 flips nothing.
* **Rollback:** delete `src/lib/nogc_sync_mut/dual_fs/`, the spec, the gate and
  the CI step. Nothing else imports them.

### R2 — repair the divergent `file_write_text` family and the name collisions

* **Surfaces:** `file_write_text`, `file_write_bytes`, `file_write_lines` in
  `nogc_sync_mut/file_system/file_ops.spl` and the `nogc_async_mut` twin;
  plus the `file_write` name collision (`database/atomic.spl:39`,
  `io/mod_stub.spl:29` — rename, per the interpreter warning's own advice).
* **Current implementation:** mocks that return `true` without writing.
* **Twin status:** **divergent, proven** — see the FAIL quoted in §1.
* **Risk:** HIGH but *inverted*. Repairing a mock makes previously-silent
  callers start performing real I/O. Some caller somewhere is relying on the
  no-op, knowingly or not.
* **Evidence required:** an effect pair per operation, green against
  `fs_write_text_native`, PLUS a call-site census of each repaired symbol so
  the newly-real writes are enumerated before they happen.
* **Rollback:** the mocks are three-line functions; revert is a single commit.
* **Note:** this release is **not owned by this lane** — it changes stdlib
  behaviour that other lanes call. R1 hands it the proof and the harness.

### R3 — Class A composition to pure Simple

* **Surfaces:** absent-parent retry, truncate-then-write ordering, atomic-write
  orchestration (`rt_file_atomic_write` policy, not the syscall), append
  semantics, line splitting/joining, error mapping to `Result`.
* **Current implementation:** partly C in `src/runtime/`, partly duplicated
  across the 10 `file_write` definitions.
* **Twin status:** none yet — write the pure twin first, pair it, then flip.
* **Risk:** MEDIUM. Ordering bugs here are exactly the class that returns a
  correct value with a wrong world, which is what the harness sees.
* **Evidence to flip the default:** effect pair green over a matrix that
  includes empty content, missing parent directory, existing file (truncate),
  read-only parent, and multi-byte content; `mode` compared, not just `size`.
* **Rollback:** flip `SIMPLE_FS_PROVIDER` back to `native`; the switch is the
  rollback mechanism, which is why it exists.

### R4 — metadata and error mapping

* **Surfaces:** `file_size`, `file_mode`, `file_modified`, `file_stat`
  interpretation; the mapping from a runtime return to `Result`/`Option`.
* **Twin status:** none.
* **Risk:** MEDIUM-LOW. Mostly total functions over an already-fetched stat.
* **Evidence:** value pairs (existing `dual_check_i64`) suffice here — no
  effect axis needed, because these operations *observe* rather than mutate.
  Say so explicitly rather than adding effect pairs that assert nothing.
* **Rollback:** per-symbol; these are leaf-callers, not orchestrators.

### R5 — digest and hash family

* **Surfaces:** `rt_file_hash`, `rt_file_hash_sha256`.
* **Current implementation:** C.
* **Twin status:** a pure-Simple SHA-256 already exists
  (`src/lib/common/crypto/sha256_core.spl`).
* **Risk:** LOW — pure function of bytes, fully value-comparable.
* **Evidence:** `dual_check_text` over the digest across a byte-length matrix
  including block-boundary lengths (55/56/63/64/65 bytes).
* **Rollback:** per-symbol.
* **Note:** `dual_fs`'s own probe deliberately uses an inline FNV-1a rather
  than this SHA-256, so the harness's oracle does not move while its own
  subject is being migrated.

### R6 — directory operations

* **Surfaces:** `rt_file_list_dir` filtering/sorting/recursion policy.
* **Risk:** MEDIUM — ordering is unspecified at the syscall and must not be
  compared as if it were stable. The effect comparison needs a
  **set** comparison for listings, which `FsEffect` does not currently model.
* **Blocked on:** extending `FsEffect` with a listing field, or a sibling
  `DirEffect`. This is a real gap, recorded here rather than assumed away.

### R7+ — the syscall floor

Not scheduled. See §6.

## 5. Per-surface table (Class A and B, the migratable ones)

| Surface | Current | Twin | Risk | Evidence to flip | Rollback |
|---|---|---|---|---|---|
| `file_write_text` | 3 divergent defs, 2 are mocks | proven divergent | HIGH | effect pair + call-site census | revert 3-line fn |
| `file_write` composition | 10 defs, C-backed retry | none | MED | effect matrix incl. missing parent | `SIMPLE_FS_PROVIDER=native` |
| `file_append_text` | C | none | MED | effect pair, size monotonic | switch |
| `file_write_lines` | mock (same file) | proven divergent | HIGH | effect pair incl. trailing newline | revert |
| `file_read_lines` | C | none | LOW | value pair (observer) | per-symbol |
| `file_atomic_write` policy | C | none | MED | effect pair + crash-window reasoning | switch |
| `file_size` / `file_mode` / `file_modified` | C | none | LOW | value pair (observer) | per-symbol |
| `file_hash_sha256` | C | `sha256_core.spl` | LOW | value pair, block boundaries | per-symbol |
| `file_list_dir` | C | none | MED | **blocked** — needs set comparison | n/a |

## 6. What CANNOT migrate to pure Simple, and why

Stated plainly rather than deferred, per `pure_simple_hal.md` §1's own framing
of C as a *boundary*:

1. **The syscall leaves themselves** — `rt_file_open`, `_close`, `_read`,
   `_write`, `_remove`, `_rename`, `_stat`, `_mode`, `_set_mode`, `_fsync`,
   `_lock`, `_unlock`, `_mmap_read_bytes`, `_canonicalize`. A syscall requires
   a register-level trap sequence. Simple has no raw-syscall provider today;
   the mechanism that would supply one is `@rt(hal, ..., providers: pure+c+rust)`
   (`doc/07_guide/language/rt_hal_attribute.md`), and it is rung 4 of the
   asm-minimization ladder — architecturally irreplaceable. Until that lands,
   `fs_write_text_pure` in this lane is honest about calling
   `rt_file_write_text`: what is pure about it is everything **above** the leaf.
2. **The C ABI surface.** Anything reached by an external C caller
   (`pub extern "C" fn rt_*` in the Rust runtime, `rt_NAME(...)` definitions in
   `src/runtime/*.c`) must keep a C-callable symbol regardless of what
   implements it, and `check-runtime-api-regression-push.shs` treats removing
   ≥5 such symbols as a FAIL. Migration here means *reimplementing behind* the
   symbol, never deleting it.
3. **SFFI marshalling** — pointer/length pairs, `[u8]` boxing, `text` encoding
   across the boundary. That code exists to satisfy a foreign ABI; expressing
   it in Simple would still require the same unsafe primitives.
4. **Bootstrap-order dependencies.** The seed compiles `src/lib` as source on
   every run; a stdlib symbol the compiler itself needs during bootstrap cannot
   depend on a provider that is only selectable at runtime.
5. **`file_list_dir` ordering** (R6) — blocked on a set-comparison effect
   model, not on the syscall.

Nothing in this list is a reason to stop; it is the line between R3–R5 (real,
schedulable) and R7 (blocked on a named, tracked mechanism).

## 7. The runnable check

```bash
sh scripts/check/check-dual-fs-effect-compare.shs                # full: selftest + spec run
sh scripts/check/check-dual-fs-effect-compare.shs --no-run       # static only (CI, no bin/simple)
sh scripts/check/check-dual-fs-effect-compare.shs --selftest-only
```

Verdict is the last line of stdout, matching the sibling gates:
`PASS — <n> check(s) run, <m> spec case(s), 0 undetected divergence(s)` exit 0 /
`FAIL — ...` exit 1 / `ERROR — nothing was checked (<reason>)` exit 2. Zero
checks, zero spec cases, or a missing `bin/simple` is ERROR, never a pass.

Measured 2026-09-06 (aarch64, seed binary):

```
selftest: 7 fixture(s) passed
census: 7 file(s) under src/lib define file_write_text (flat registry keyed on name alone)
PASS — 10 check(s) run, 6 spec case(s), 0 undetected divergence(s)
```

**The gate bites.** Running the spec is not enough on its own — a spec can be
gutted to trivially-true assertions and stay green forever — so the gate also
requires the discriminating assertions to still be present. Proven against a
real gutted copy:

```
FAIL — 10 check(s) run, 6 spec case(s), spec-assertion-missing:effect_divergence_asserted
```

Selftest fixture (d) replays exactly that shape, so the requirement cannot
rot into dead code.

**Wiring:** the CI step lives in `.github/workflows/repo-hygiene.yml`, job
`Code Idiom & Structural Ratchet Gates` (a required status check).
`check-guard-wiring.shs` confirms the guard is reachable — it does not appear
in that gate's unwired list.

**Honest limitation, same as the value-comparing sibling:** this dual-runs
inside specs and tools, not on live production traffic, and `diff` mode costs
two writes and two probes per operation. It is a verification mode, not a
default.
