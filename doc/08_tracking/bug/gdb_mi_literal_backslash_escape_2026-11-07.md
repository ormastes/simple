# GDB MI escaped literal backslashes are reinterpreted as control escapes

Status: isolated source repair; executable regression pending.
Owner: src/lib/nogc_async_mut/debug/remote/protocol/gdb_mi_parser.spl, GdbMiParser.unescape_mi_string.

The chained replacement decoder processes backslash-n/backslash-t before escaped backslashes. Thus a valid C-string encoding of a Windows path containing a literal backslash followed by n or t can be corrupted into a control character. Resident Windows GDB inspection reaches this helper for MI fullname/value/stream strings, so copying it unchanged would corrupt real paths.

The candidate decoder consumes each escape once and copies complete intervening UTF-8 spans. It preserves the existing unknown-escape behavior and adds carriage-return decoding. The existing public API is unchanged. Regression cases use the real helper and the immutable MI adapter to distinguish literal Windows path backslashes from actual newline escapes; they are prepared at test/01_unit/app/mcpgdb/resident_mi_value_spec.spl. They have NOT run, and no GDB/target qualification is implied.
