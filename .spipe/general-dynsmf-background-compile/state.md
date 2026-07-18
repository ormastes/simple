# Feature: general-dynsmf-background-compile

## Raw Request
$sp_dev then update it and complete as my expectaion and update releated docs, guide, and spipe skills to next time not to skip and make it general implmentation.

Context from the thread: the intended feature is to compile SMF artifacts while the interpreter reads/runs scripts. It was first intended for GUI libraries, but the implementation must be general and discoverable for future agents.

## Task Type
feature

## Refined Goal
Generalize dynSMF startup so interpreter-mode script startup can request non-blocking SMF compile work for any manifest entry, records evidence for that background compile request, and documents the canonical workflow outside the GUI-only lane.

## Acceptance Criteria
- AC-1: dynSMF manifests expose enough source/output metadata for non-GUI and GUI entries to produce deterministic `bin/simple compile <source> -o <artifact>.smf` work items.
- AC-2: startup dynSMF code can request background compile work while preserving interpreter progress and records explicit evidence rows for queued, skipped, invalid, and already-ready artifacts.
- AC-3: checked autoload remains artifact-safe: missing or invalid SMFs are not silently treated as loaded, and background compile evidence does not mask load failures.
- AC-4: unit or integration specs cover the general background compile behavior for at least one non-GUI library and one GUI-related library.
- AC-5: docs, guides, and SPipe/Codex skills name this as the general dynSMF background compile lane so future work does not skip it or treat it as GUI-only.
- AC-6: focused verification commands and the generated-spec layout guard pass or any failures are recorded with concrete evidence.

## Scope Exclusions
- No OS-thread process supervisor is required in this pass; the implementation may model and emit background compile work/evidence without spawning unmanaged compiler processes from interpreter startup.
- No change to SMF binary format is required.
- No release, tag, or push is required.

## Phase
verify-done

## Log
- dev: Created state file with 6 acceptance criteria (type: feature).
- impl: Added general dynSMF background compile evidence APIs in `src/os/smf/dynsmf_session.spl`.
- impl: Wired `src/app/startup/dynsmf_autoload.spl` to queue missing dynSMF compile work before checked autoload.
- impl: Added explicit-manifest startup helper and exported it through `src/app/startup/__init__.spl`.
- spec: Updated `test/01_unit/os/smf/dynsmf_session_spec.spl` and `test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl`.
- docs: Updated low-dependency dynSMF architecture/design/test-plan docs, TLDRs, generated spec docs, `doc/07_guide/lib/api/dynlib_api.md`, `.claude/skills/spipe.md`, `.codex/skills/sp_dev/SKILL.md`, and `.codex/skills/system_test/SKILL.md`.
- verify: `test/01_unit/os/smf/dynsmf_session_spec.spl --mode=interpreter` passed once normally and clean rerun log shows file PASSED before sandbox timeout truncated the summary.
- verify: `SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple src/compiler_rust/target/bootstrap/simple test test/02_integration/app/simple/dynsmf_autoload_policy_spec.spl --mode=interpreter` passed with 6 scenarios.
- verify: `SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple sh scripts/check/check-low-dependency-dynsmf-build-plans.shs` passed; 6/6 dynSMF compile plans compiled with `SMF\0` magic.
- verify: focused `simple check` passed for `src/os/smf/dynsmf_session.spl`, `src/app/startup/dynsmf_autoload.spl`, and `src/app/startup/__init__.spl`.
- verify: `sh scripts/setup/install-spipe-dev-command.shs --check` returned `STATUS: PASS`.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
