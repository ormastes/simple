# Feature: native-build-env-timeout

## Raw Request

let it to be configurable timeout on system env not just increase it on code but let to referedcne env valude and set env valuee since it run variouse env. and add to spipe skill and the code log print and llm wiki that timeout canbe cahnged by env value and other times out to use same way rather fix the value on code. add agents improve simple arg library not oly it can start up parseing file special feature it make env variable reference feature uto matically check other arg libs. can start with module or exceutalbe name with capital with _

## Task Type

feature

## Refined Goal

Provide a shared native-build argument environment-resolution contract so each executable or module can configure timeout policy through uppercase `SIMPLE_<SCOPE>_<OPTION>` variables without hard-coded host-specific values.

## Acceptance Criteria

- AC-1: Native-build resolves a documented per-file timeout environment value with explicit CLI precedence and a safe default when the variable is absent or invalid.
- AC-2: The shared argument library derives and validates uppercase `SIMPLE_<MODULE_OR_EXECUTABLE>_<OPTION>` names without accepting arbitrary unrelated environment variables.
- AC-3: Native-build startup logs the effective timeout, source (CLI, scoped environment, or default), and rejected environment reason without exposing unrelated environment values.
- AC-4: Existing timeout-bearing argument owners are audited and either use the same resolution helper or record a precise reason and follow-up.
- AC-5: Focused executable specs cover CLI-over-environment precedence, valid scoped environment values, invalid-value rejection, and module/executable scope normalization.
- AC-6: The SPipe skill and the matching LLM/operator documentation explain the environment contract, precedence, naming, and verification command.
- AC-7: Existing Vulkan and bootstrap authority behavior remains fail-closed; no Rust seed or stale artifact is accepted as live Vulkan evidence.

## Scope Exclusions

- No global environment-variable scan or automatic adoption by unrelated commands without an owning argument surface.
- No weakening of live Vulkan, provenance, or timeout failure behavior.

## Cooperative Review

- Sidecars: argument-library audit, timeout-owner inventory, and documentation-mirror inventory.
- Merge owner: Codex `/root`.
- Final reviewer: normal/high-capability Codex review after sidecar findings.
- Shared interface: `SIMPLE_<MODULE_OR_EXECUTABLE>_<OPTION>`; native-build effective-timeout receipt.
- Scenario helpers: `Given_scoped_timeout_environment`, `When_native_build_resolves_timeout`, `Then_timeout_receipt_reports_source`.
- Setup/checker helpers: `native_build_env_timeout`, `native_build_timeout_receipt`.
- Fail-fast placeholder: `fail("native-build timeout environment contract is not implemented")` until the executable scenario is wired.
- Generated-manual review owner: Codex `/root`.

## Phase

dev-done

## Log

- dev: Created state file with 7 acceptance criteria (type: feature).
