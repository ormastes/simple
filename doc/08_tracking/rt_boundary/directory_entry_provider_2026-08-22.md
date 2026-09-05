# Directory entry runtime provider classification

Status: classified provider, 2026-08-22.

`src/lib/nogc_sync_mut/io/dir_entry_ops.spl` owns the hosted directory-stream
and status-code ABI for `readdir`, mode-aware `mkdir`, and empty-directory
removal. These primitives have no lower Pure Simple host implementation. The
file may bind and call its private `rt_*` symbols; consumers may not import
them.

The public surface is the signature-preserving semantic wrapper set:
`directory_stream_open`, `directory_stream_count`, `directory_stream_entry`,
`directory_stream_close`, `directory_create_mode`, and `directory_remove`.
Keeping the raw status values preserves `AsyncDir` error classification while
removing all raw-runtime names from that product consumer.
