# Feature: simplebox-entry-abi

## Raw Request

Primary SimpleOS Linux tools must be implemented in Simple and launchable from the filesystem.

## Task Type

bug

## Refined Goal

Make the SimpleBox filesystem payload use the canonical freestanding SimpleOS entry ABI.

## Acceptance Criteria

- AC-1: `simplebox_main.spl` exposes a zero-argument `main` that obtains runtime arguments once through `get_args()`.
- AC-2: all existing applet dispatch and status behavior remains delegated to `simplebox_run`.
- AC-3: the focused source check accepts the entry source.
- AC-4: media staging, signed catalog admission, and generic launcher routing remain active separate requirements; this change does not represent filesystem-launch proof.
- AC-5: developer-guide and LLM-wiki updates are N/A because this corrects the existing documented entry ABI in one payload; the source comment records the boundary contract.

## Scope Exclusions

No compiler bootstrap, payload staging, catalog signing, or launcher-policy bypass.

## Cooperative Review

N/A: narrow ABI correction; the earlier high-effort campaign review identified this exact source-level blocker.

## Phase

impl-done-unverified-runtime

## Log

- dev/impl: Replaced unsupported typed entry `main(argv: [text])` with `main() -> i32` and `get_args()`.
- evidence: `bin/simple check src/os/tools/simplebox/simplebox_main.spl` passed. The command emitted the bootstrap-seed warning, so no deployed target runtime claim is made.
