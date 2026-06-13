# Feature: qemu_storage_docs

## Raw Request
minimize qemu ssd storage overhead if possible; update doc, guide, spipe, skill (goal 2026-06-13).

## Task Type
code-quality

## Refined Goal
A storage audit script reports reclaimable QEMU artifacts with a documented retention policy, and the QEMU system-test workflow is documented in guide + spipe skill.

## Acceptance Criteria
- AC-1: scripts/check/qemu-storage-audit.shs prints per-category bytes (FAT32 imgs, kernel ELFs, QMP logs, stale serial logs, FreeBSD VM overlays, duplicate probe images) and total reclaimable; supports --clean for safe categories (stale QMP/serial logs older than 7 days, duplicate probe imgs) with dry-run default.
- AC-2: doc/07_guide/platform/simpleos/qemu_system_tests.md exists: per-arch run instructions, direct-boot fallback while P1 open, marker contracts, storage policy.
- AC-3: .claude/skills/spipe.md (or lib/spipe_phases.md) gains a concise system-test-over-qemu section referencing the new specs/helper.
- AC-4: Running the audit on this host shows before/after numbers if --clean executed; nothing under git tracking deleted.

## Scope Exclusions
Do not delete FAT32 images or kernel ELFs. No qemu_runner changes. No test changes.

## Phase
dev-done

## Log
- dev: Created state file with 4 acceptance criteria (type: code-quality)
