# W-MC-RES-001 over-fires ~208 findings; verb-only heuristic cannot separate handle acquires from value constructors

**Status:** OPEN. **Filed:** 2026-08-07. Rule: `W-MC-RES-001
unwrapped_foreign_resource` (REQ-MC-023), implemented in
`src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`.

## First: the rule is LIVE, not dormant

Both `doc/02_requirements/language/mission_critical_profile.md` (REQ-MC-023
"**Status: IMPLEMENTED, DORMANT pending lint redeploy (WP-3.5)**") and
`doc/00_llm_process/feature_expert/resource_ownership/skill.md` (two places)
claimed the checker "fires for nobody" until a lint redeploy. **That is no
longer true** — corrected in the same change as this file. Positive
capability probe, not inference:

```
$ bin/simple lint --profile=critical /tmp/.../res_probe.spl
res_probe.spl:5:0: warning[W-MC-RES-001]: bare foreign-resource handle escapes via return without a wrapping constructor
```

Controls run at the same time, all behaving correctly:

| probe | result |
|---|---|
| bare acquire returned, `--profile=critical` | **fires** (as designed) |
| same wrapped in an owning `class` constructor | silent |
| same wrapped in a **refcounted** class (`handle` + `refs`) | silent |
| bare acquire, `--profile=moderate` | silent (correctly critical-only) |

The refcount row answers a standing question: **an RC wrapper is already
accepted as compliant**, incidentally — the accept predicate takes any
`TypeName(...)` constructor call, so it does not need to distinguish affine
from refcounted ownership. No code change was needed for "ownership **or**
ref count"; only the requirement text needed to say so.

## The defect

**Update (same day): the sound part of this is now FIXED — see "Landed fix" below.**

Swept over all 245 owned-code `.spl` files containing an acquire-verb `rt_*`
call: **208 findings across 78 files.** The overwhelming majority are false
positives, because the check matches on the acquire **verb alone**
(`acquire_verbs()` = open/create/new/alloc/acquire/copy/clone/load) and never
establishes that the call returns an **opaque handle** at all.

Composition of the flagged calls by verb:

| verb | count |
|---|---|
| `new` | 63 |
| `create` | 29 |
| `load` | 24 |
| `alloc` | 18 |
| `copy` | 11 |
| `clone` | 9 |
| `acquire` | 1 |

Concrete false positives, all confirmed by reading the source:

- `src/runtime/simple_core/core_string.spl:198` — `val out = rt_string_new(data, len)`.
  Returns a **string value**; this is the runtime implementing strings.
- `src/runtime/simple_core/core_string.spl:216` — `return rt_array_new(0)`.
  Returns an empty **array value**.
- `src/app/game/new.spl:24` — `rt_dir_create(path, true)`. Creates a
  directory and returns **bool**. No handle exists to wrap.
- `src/lib/nogc_sync_mut/atomic.spl` — `rt_atomic_int_load` is an atomic
  **read**, not an acquire; `load` collides with the acquire-verb catalog.

So the false positives are *not* confined to the runtime/std wrapper layer —
`rt_dir_create` is ordinary application code. A path-based carve-out would
therefore not fix this, only relocate it.

## Why the obvious narrowing is UNSOUND — do not ship it

The natural fix is "only flag a family that has a paired release extern"
(the doc's own definition of a resource, and what WP-D's fail-closed
`infer_family_conventions` already computes). Measured: of the 34 distinct
flagged calls, 18 have a same-prefix release and 16 do not — so it would cut
roughly half the noise.

**But it fails open on real resources.** Among the 16 it would silence:

- `rt_io_tcp_socket_create` — a socket, unambiguously needs closing.
- `rt_cuda_module_load` — a CUDA module, likewise.

Their releases exist under a *different* prefix, so same-prefix pairing
misses them. Trading ~90 false positives for a silent miss on socket and
CUDA-module leaks is the wrong direction for a safety rule: noise is
visible, a false negative is not. Pairing also does **not** filter the
biggest offenders anyway — `rt_string_free`, `rt_array_free` and
`rt_atomic_int_free` all exist, so strings, arrays and atomics stay flagged.

## What a sound fix needs

The missing input is **type information**: whether the acquire's return
value is an opaque handle rather than a value (`bool` for `rt_dir_create`,
a string/array for `rt_string_new`, an int for `rt_atomic_int_load`). A
text-level, verb-matching check cannot obtain that, and no arrangement of
verb lists or path filters substitutes for it.

That information is exactly what the `@sffi(handle: ...)` metadata and the
`resource R` declaration were designed to carry, and WP-A/WP-C already land
the registry that holds it (`compiler.frontend.resource_registry`). The
sound version of this rule is a **semantic** check keyed on a declared
handle type, not a text scan keyed on a name suffix.

## Consequences to respect until then

- **Do not promote REQ-MC-023 to `deny` at profile v2** on the current
  implementation. At 208 findings dominated by string/array/atomic
  constructors, deny would fail the tree on correct code. The warn→deny
  phasing decision (dated 2026-08-07) should be re-evaluated only after the
  semantic rework.
- **Do not "fix" the 208 findings by wrapping them.** Most name no resource;
  wrapping `rt_string_new` or `rt_dir_create` would be nonsense churn.
- The rule remains useful as-is for the case it genuinely catches —
  e.g. `src/compiler/70.backend/sffi_minimal.spl:178,181,253`.

## Measurement harness (reproduce)

`bin/simple lint` costs ~14 s/file here (550 s reached only 3 of 40 files,
exit 124 — and it still printed a summary line, so its output is a
false-completion trap; read the exit code, not the tail).

Instead drive the checker directly, as a plain script — **not** a spec: the
test daemon's startup cap fires while loading the compiler lint module tree,
before any scanning happens (`ERROR: test daemon timed out`), and
`dir_walk("src")` does not terminate under the interpreter (same as WP-16).

```
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <harness>.spl   # ~exit 0, whole sweep
```
calling `check_unwrapped_foreign_resource(file_read(p), p)` over a
pre-narrowed candidate list. Full 245-file sweep completes this way.

**Cross-validated:** the harness reproduces the real lint's own output
exactly on the one file `bin/simple lint` did reach —
`sffi_minimal.spl` lines 178, 181, 253 — which is what makes the 208 credible.
Note `UnwrappedResourceFinding`'s line field is `line_num`, not `line`.

## Landed fix: return-type gate (208 -> 160)

`_ufr_is_nonhandle_return_type` + `_ufr_nonhandle_externs` now parse the
`extern fn NAME(...) -> TYPE` declarations in the file being checked and
suppress an acquire-verb call whose declared return type **cannot** be an
opaque handle. Sweep: **208 -> 160 findings, 78 -> 51 files.**

Deliberately narrow, and fail-closed in three ways:

- Only `bool` and concrete array types (`[u8]`, `[i64]`, ...) qualify.
- **`Any` is NOT treated as a non-handle** — `rt_mutex_new` and
  `rt_rwlock_new` both return `Any`, so excluding it would fail open on real
  resources. A spec pins this (`still flags when the return type is Any`).
- An extern with no declaration in the file keeps being flagged: no type
  information is not a licence to go quiet. Also spec-pinned.

Every one of the 48 removed findings was verified to be one of 8 provably
non-handle externs — `rt_dir_create` (19) and `rt_file_copy` (11), both
`-> bool`; `rt_bytes_alloc` and the four `rt_*_array_alloc` (arrays);
`rt_atomic_bool_load` — plus 9 handle-vars bound from those same calls.
**No `rt_file_open`, `rt_image_load`, socket or CUDA finding was affected**,
and the lint-cross-validated true positives at `sffi_minimal.spl:178,181,253`
all survive. Sabotage-verified: stubbing the predicate to `false` restores
exactly 208, reverting gives 160 again. Spec 22/22 (5 new).

## What is still open after that fix

160 findings remain, still dominated by `rt_string_new` / `rt_array_new`
(both `-> i64` with a genuine `_free`). Separating those from a real handle
acquire needs the declared handle type from `@sffi(handle: ...)` /
`resource R` — and **there are currently ZERO `resource` declarations in
`src/`** (only 6 files mention `@sffi` at all), so that registry is empty and
a check keyed on it today would be vacuous. That is the blocker for the rest,
and it is the same blocker as the wider migration: the seed cannot parse
`resource` syntax in production source. The v2 `deny` promotion stays blocked.

**Re-verified 2026-08-10:** the return-type gate (`_ufr_is_nonhandle_return_type`
/ `_ufr_nonhandle_externs`, `unwrapped_foreign_resource.spl:161,168`) is still
present and unreverted. `grep -rn "^resource " src/lib src/app src/compiler`
now finds **7** matches (up from the 0 measured when this doc was filed) —
some `resource` declarations now exist, so the registry is no longer
literally empty, but this was not re-measured against the seed's parse
capability or the lint checker's actual consumption of that registry in this
pass, so it is noted as a fact, not treated as closing the blocker. The
164-finding residual and the `deny`-promotion block remain open.

## Re-verification 2026-08-17

Re-read `src/compiler/35.semantics/lint/unwrapped_foreign_resource.spl`
(within scope). Confirmed still present and unchanged from the doc's
description: `_ufr_is_nonhandle_return_type` (line 161) and
`_ufr_nonhandle_externs` (line 168) implement the same-file, text-level
`extern fn ... -> TYPE` return-type gate exactly as documented (`bool` and
`[`-prefixed array types only; `Any` deliberately excluded).

`grep -rn "^resource " src/lib src/app src/compiler` returns 7 matches (same
count the doc's 2026-08-10 note recorded). The blocker is unchanged: the
sound fix needs a populated `@sffi(handle: ...)` / `resource R` registry
(`compiler.frontend.resource_registry`) consulted by the checker, and that
registry — its population and its consumption path — is not owned by
`unwrapped_foreign_resource.spl`; wiring it is a cross-cutting change that
the doc itself frames as belonging to WP-A/WP-C plus the checker's dispatch
into the lint rule registry (out of scope per this task's instructions: "if
the real fix requires editing the shared lint rule REGISTRY ... do NOT touch
it").

No further narrowing was attempted within `unwrapped_foreign_resource.spl`
alone: any additional cut (e.g. adding more non-handle return types, or
special-casing `rt_string_new`/`rt_array_new` by name) would be exactly the
kind of unsound, ad hoc narrowing the doc explicitly warns against ("do not
ship it") without real type information from the (currently unconsumed)
resource registry.

**Verdict: SKIPPED-CLAIMED / BLOCKED — the return-type gate already landed
inside this file (in-scope, already done); the remaining 160-finding residual
needs the resource-registry consumption wiring, which crosses into the
shared lint-rule-dispatch machinery this worker was told not to touch. No
code change made in this pass.**
