# Critical Completeness — Frozen Language Contract (Phase 0 lock)

Normative list of the contract items frozen by Phase 0 of
`doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`
(design: `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`).
Each row names the item and the ONE file that embodies it. `UNLANDED` means the
contract is specified here but no code/spec artifact exists yet; the lock gate
does not require UNLANDED rows to exist, it requires this list to not drift.

Lock gate: `sh scripts/check/check-completeness-contract-lock.shs`.
The artifact list this doc and its sibling name is hashed into
`spec/compiler_schema/contract_lock.sdn`; changing any row below without
updating that file is a FAIL.

## 1. Closure states

| Item | Contract | Embodied by |
|---|---|---|
| `static` | closes at compiler build; exhaustive at compile time | `src/compiler/00.common/dynamic_identity/closure.spl` (`Closure.Static`) |
| `complete` | closes at config/link/seal; exhaustive at the seal | same (`Closure.Complete`) |
| `dyn` | never closes while running; no whole-world proof | same (`Closure.Dyn`) |

Rule: a `critical` build admits `static` and `complete` only; `dyn` is a
diagnostic (`E-MC-DYN-001`, design §17).

## 2. Linkage and activation axes

| Axis | Values | Embodied by |
|---|---|---|
| linkage | `static_link`, `dynload` | `src/compiler/00.common/dynamic_identity/closure.spl` (`Linkage`) |
| activation | `startup`, `first_use`, `command`, `manual`, `hotspot` | same (`Activation`) |
| manifest axes parse | `closure:`/`linkage:`/`activation:` keys | `src/compiler/99.loader/completeness_seal/axis_parse.spl` |

## 3. Any capability and escape rule

| Item | Contract | Embodied by |
|---|---|---|
| `type_erasure` capability | only unsafe region that may hold `Any` | `src/compiler/00.common/assurance/unsafe_capabilities.spl` (`UnsafeCapability`) |
| frontend erasure marker | `Any` origin tagging | `src/compiler/10.frontend/core/type_erasure.spl` |
| escape rule | `Any` outside a granted region = `E-MC-ANY-001`; erased value leaving a region = `E-MC-ANY-002`; checked downcast result may leave | `src/compiler/35.semantics/any_escape/checker.spl`, `types.spl` |
| census (ratchet) | frozen population, growth and stale baseline both FAIL | `scripts/check/check-any-escape-census.shs`, `scripts/check/any_escape_baseline.txt` |

## 4. Diagnostic id ranges

| Prefix | Family | Embodied by |
|---|---|---|
| `E-MC-ANY-0xx` | Any origin/escape | `src/compiler/35.semantics/any_escape/types.spl` |
| `E-MC-DYN-0xx` | dyn closure in critical build | design §17 only — `UNLANDED` |
| `FV2-E-ASPECT-*` | aspect proof/seal | `src/compiler/00.common/assurance/formal_interfaces.spl` |
| generated per-enum ranges | one range per registry enum | design §11 — `UNLANDED` |
| `E-GRAMMAR-ORPHAN-TAG` / `E-GRAMMAR-DEAD-PRODUCTION` | grammar-axis cross-check: every flat-AST tag is stamped by >=1 parser production, and every production is reachable | `src/app/compiler_schema/grammar_extract.spl`, `spec/compiler_schema/registry/compiler.frontend.Grammar.sdn` (gate: `scripts/check/check-compiler-schema-fresh.shs`) |

## 5. Evidence receipt format

| Item | Contract | Embodied by |
|---|---|---|
| proof receipt | `proof_receipt_hash` required, framed by `_formal_interface_frame_v1` | `src/compiler/00.common/assurance/formal_interfaces.spl` |
| gate verdict line | `PASS — <n> ... / FAIL — ... / ERROR — nothing was checked (<reason>)`, last stdout line, n > 0 | every check script named in these docs (see §3 census row) |

## 6. Out of scope here

Compiler-side items (extension identity, `CoverageState`, mono keys, aspect
seal schema, registry format) are frozen in
`doc/04_architecture/compiler/extension_completeness.md`.
