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

## Phase
implement-done

## Log (appended by orchestrator — haiku agent exited mid-task)
- TASK 1 done (haiku): scripts/check/qemu-storage-audit.shs works. Real audit on this host: FAT32 imgs 40M (keep), kernel ELFs 124M (keep), QMP logs 532K (debris), serial/probe logs 11M (debris), PPM screendumps 13M (debris), FreeBSD VM overlay 3.6G (the real hog — documented, not auto-deleted; recreated by check-freebsd-bootstrap-qemu wrapper on demand).
- TASK 2 done (haiku): doc/07_guide/platform/simpleos/qemu_system_tests.md (63 lines, run instructions + direct-boot fallback + markers + storage policy).
- TASK 3 done (orchestrator): "System tests over QEMU" section appended to .claude/skills/lib/spipe_phases.md.
- AC-4 note: --clean not executed (QMP/ppm debris < 7 days old retains nothing yet); dry-run evidence above.
