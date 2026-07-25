# FAT32 Long-Filename Read Contract

Executable source:
`test/01_unit/lib/fs_driver/fat32_core_lfn_spec.spl`.

## Scope

The shared pure-Simple FAT32 reader accepts printable-ASCII VFAT long names on
prebuilt media. It validates slot order, LAST markers, reserved metadata, the
8.3 checksum, and the 255-character limit before publishing a long name.
Unsupported Unicode and malformed chains remain accessible only through their
exact 8.3 aliases. Creating or renaming LFNs in the guest is outside this read
contract.

## Operator walkthrough

1. Mount the in-memory FAT32 image through `Fat32Core`.
2. List and resolve one-slot, two-slot, nested, and cross-cluster long names.
3. Resolve the same files through their exact 8.3 aliases.
4. Confirm a 255-character name is accepted and a 260-character name is not.
5. Corrupt order, checksum, metadata, character encoding, or chain continuity;
   confirm the long name disappears while the 8.3 alias remains readable.
6. Remount replacement media and confirm cached names do not survive.
7. Mount the same image through SimpleOS `SharedFat32Driver`, then exercise
   `readdir`, `stat`, `open`, `read`, and `close` on the long path.

## Expected evidence

| Area | Required observation |
|---|---|
| Valid chain | The published `DirEntry.name` is the assembled long name. |
| Boundary | 255 characters resolve; 260 characters fall back to 8.3. |
| Corruption | No malformed or interrupted chain becomes a visible LFN. |
| Nested path | Directory and leaf LFNs resolve case-insensitively. |
| Media change | Old cached LFNs are absent after unmount and remount. |
| SimpleOS route | Shared adapter operations return the long-name file payload. |

## Current execution status

The source scenarios and static guards are present. This worktree has no
`bin/simple`; one cached self-hosted `Simple v1.0.0-beta` run exited 139 without
diagnostics. See
`doc/08_tracking/bug/self_hosted_fat32_lfn_interpreter_segv_2026-07-14.md`.
A Rust bootstrap seed is not admissible evidence.
