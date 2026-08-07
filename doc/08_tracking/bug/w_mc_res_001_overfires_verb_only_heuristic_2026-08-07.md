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
