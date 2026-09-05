# Test plan — Engine2D font offload fallback and user-`Option` lowering system lane

**Lane:** `restart12_engine2d_font_seed_review`
**Base revision:** `f6cadcc36aff61d16d988651ea36a040d2af6aad`
**Status:** coverage authored, fail-closed, unexecuted (toolchain blocked)

## Why this lane exists

Two changes landed on `origin/main` and were reviewed structurally:

| Commit | Subject | Review outcome |
|---|---|---|
| `b10f1b4309c` | `fix(engine2d): recover font offload fallback fixes` | **Sound.** Repairs a call to `backend_canonical_name`, a symbol defined and imported nowhere in `backend_lane.spl`; all three call sites now use `_engine2d_backend_canonical_name`. The `.initialized` guard added to the Vulkan route is correctly scoped — Vulkan is the only arm where `self.backend` can diverge from a non-nil sibling field. |
| `8d96687c991` | `fix(seed): match builtin Option None in HIR lowering` | **Defect found.** The builtin-`Option` exception is keyed on `name == "Option"`; both runtimes key on the reserved enum id. Filed as `doc/08_tracking/bug/seed_builtin_option_name_heuristic_breaks_user_option_enum_2026-08-16.md`. |

Neither had system-level coverage. This plan adds it.

## Scope

In scope:
- Engine2D configured-font execution: fallback order and attempt ledger, observed through a native binary.
- Match lowering for a user-declared enum named `Option` with the `Some(payload)`/`None` shape.

Out of scope (deliberately not broadened):
- Glyph raster correctness, GPU residency, presentation, performance.
- Generic `Option<T>` inference, `Result` lowering.
- The rocm `self.backend` hijack asymmetry noted during the audit (`engine.spl` L1700, L1941, L2006) — a different failure direction, not reachable from any current construction path. Follow-up, not this lane.
- Any change to Engine2D source. The audit concluded none is warranted.

## Artifacts

| Artifact | Path |
|---|---|
| Admission gate | `test/03_system/qualified_pure_simple_runtime.spl` |
| Engine2D system spec | `test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl` |
| Lowering system spec | `test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl` |
| Engine2D fixture | `test/fixtures/engine2d_font_offload_fallback/main.spl` |
| Lowering fixture | `test/fixtures/user_option_enum_match/main.spl` |
| Mirrored manuals | `doc/06_spec/03_system/lib/gpu/engine2d/…md`, `doc/06_spec/03_system/compiler/…md` |

## Requirements traceability

| REQ | Assertion | Spec |
|---|---|---|
| REQ-E2DFONT-001 | Suggested-policy draw reports painted | engine2d font offload |
| REQ-E2DFONT-002 | Ledger equals the documented order and terminates on `cpu:success` | engine2d font offload |
| REQ-E2DFONT-003 | Preferred policy walks the same order | engine2d font offload |
| REQ-OPTLOWER-001 | User `Some(42)` binds its payload | user-`Option` lowering |
| REQ-OPTLOWER-002 | User `None` reaches its own arm (`99`) | user-`Option` lowering |
| REQ-OPTLOWER-003 | `Some` arm stays refutable against `None` | user-`Option` lowering |

## Fail-closed policy

Both specs route runtime admission through
`admit_pure_simple_runtime()`, which **fails** — never skips — when:

1. `SIMPLE_QUALIFIED_RUNTIME` is unset or empty;
2. the named binary emits no `--version` banner (unidentifiable);
3. the banner self-identifies as the Rust bootstrap seed.

A second gate, `require_runtime_can_native_build()`, fails with the compiler's
own stderr when the admitted runtime cannot build the fixture — so a
segfaulting compiler is never mistaken for a failing assertion about the
subject under test.

## Execution status — honest

**These specs have never been executed and are expected to fail today.**

No qualified pure-Simple runtime exists on the reference machine. A fleet-wide
sweep on 2026-08-16 enumerated 1099 binary instances, 19 unique by md5:
14 are the Rust seed (disqualified), and all 5 self-hosted artifacts are
non-functional — two segfault on a three-line hello world, one emits no
artifact while returning success, one cannot resolve the SSpec DSL and requires
delegation to a seed sibling, one is Mach-O arm64. Detail and the per-candidate
table:
`doc/08_tracking/bug/stage3_native_build_segv_two_distinct_faults_tagged_value_seam_2026-08-11.md`.

No runtime PASS is claimed for any criterion in this lane.

## Unblock condition

`.spipe/stage3-segfault-fix/` AC-3 (Stage 3 exits 0) and AC-4 (the receipted
candidate compiles and runs a program) close, or any other route to a
self-hosted `simple` that can `native-build`. Then:

```sh
SIMPLE_QUALIFIED_RUNTIME=/abs/path/to/simple \
  <runtime> test test/03_system/lib/gpu/engine2d/engine2d_font_offload_fallback_system_spec.spl
SIMPLE_QUALIFIED_RUNTIME=/abs/path/to/simple \
  <runtime> test test/03_system/compiler/user_option_enum_match_lowering_system_spec.spl
```

Expect REQ-OPTLOWER-002 and REQ-OPTLOWER-003 to **fail** until the
name-heuristic defect is repaired — that failure is the point of the fence.

## Stop rule

Maximum three verify/fix cycles per criterion; a blocker is reported, not
looped on. This lane consumed its cycles establishing that the runtime is
unavailable and stopped.
