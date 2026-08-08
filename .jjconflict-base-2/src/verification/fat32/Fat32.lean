-- Fat32 — Lean 4 formal model of the SimpleOS FAT32 filesystem invariants.
-- Wave-4a/4b/4c; plan: doc/03_plan/runtime/hardening_formal_verification_2026-06-11.md
-- Source of truth:
--   src/os/kernel/fs/fat32.spl          (Fat32Filesystem driver)
--   src/os/kernel/types/fs_types.spl    (FileHandle, FileStat, Fat32Bpb)
-- Zero sorry in this project (findings recorded as comments, not sorry).
import Fat32.Basic
import Fat32.Theorems
