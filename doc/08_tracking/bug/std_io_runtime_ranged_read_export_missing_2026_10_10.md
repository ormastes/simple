# std.io_runtime ranged read export missing

Status: OPEN; source repair and four regression cases authored, UNEXECUTED.

Caret Phase4 HIR with Phase2 producer aa404 and a0 sources reported missing file_read_text_at_nullable in native_formats.spl. The physical io_runtime owner already defines and exports the checked operation, but the root facade shadows that module and omits it. The repaired facade exposes the same declaration via the SoSix host facade, under its existing name and a sosix alias, with no additional native wrapper or application host calls.

Tests: test/01_unit/lib/std_io_runtime_ranged_read_spec.spl; fixture test/fixtures/io_runtime/ranged_read_ascii.txt. These assert exact ranged bytes through both names, negative offset, missing positive-size read and existing-file zero-size read. Runtime code is unchanged: host_path_native and checked provider own Windows binary file reads, POSIX reads and platform errors; macOS/FreeBSD/SimpleOS execution remains unverified. No essential binary or runtime is qualified by this source repair.
