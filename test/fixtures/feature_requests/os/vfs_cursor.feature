# Feature: FsDriver VfsCursor select-file cursor (FR-SIMPLEOS-M5-001)
# Anchors: FR-SIMPLEOS-M5-001 — stateful cursor for iterating VFS directory entries
# Target: src/lib/nogc_sync_mut/fs/ (FsDriver, VfsCursor), SimpleOS kernel VFS layer
# Status: pending — wave 8 impl must satisfy these contracts.

Feature: VfsCursor provides stateful iteration over VFS directory entries
  As a SimpleOS kernel engineer
  I want a VfsCursor that opens on a directory and advances entry-by-entry
  So that userland can list files without holding directory locks across syscalls

  Background:
    Given a mounted FAT32 volume at path "/vol"
    And   directory "/vol/data" containing files: "alpha.txt", "beta.bin", "gamma.log"

  Scenario: Golden path — open cursor and iterate all entries
    Given FsDriver is initialized and "/vol/data" exists
    When  I call "VfsCursor::open(path: '/vol/data')"
    Then  the cursor is in the Open state
    And   successive calls to "cursor.next()" return DirEntry for "alpha.txt", "beta.bin", "gamma.log" in stable order
    And   the final "cursor.next()" call returns None (end of directory)

  Scenario: Cursor close releases directory handle
    Given an open VfsCursor C on "/vol/data"
    When  I call "C.close()"
    Then  the cursor transitions to the Closed state
    And   any subsequent "C.next()" call returns Err(FsErr::CursorClosed)
    And   the directory handle is released so the directory can be modified

  Scenario: Cursor open on non-existent directory returns NotFound
    When  I call "VfsCursor::open(path: '/vol/missing')"
    Then  the call returns Err(FsErr::NotFound)
    And   no cursor object is created

  Scenario: Cursor open on a file (not directory) returns NotADirectory
    Given a file "/vol/data/alpha.txt" exists
    When  I call "VfsCursor::open(path: '/vol/data/alpha.txt')"
    Then  the call returns Err(FsErr::NotADirectory)

  Scenario: Cursor survives concurrent file creation in the directory
    Given an open VfsCursor C positioned after "alpha.txt"
    When  a concurrent operation creates "/vol/data/delta.dat" while C is open
    Then  C may or may not yield "delta.dat" (implementation-defined snapshot semantics)
    And   C does NOT crash or return a corrupted DirEntry
    And   all entries present before the cursor was opened are returned exactly once
