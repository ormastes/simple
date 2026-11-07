# Windows process hash cleanup loses failed native resource identities

Status: OPEN, source finding only; native reproduction NOT_RUN.

`_windows_process_hash_handle_v1` in
`src/lib/nogc_sync_mut/io/windows_process_owner.spl` sets `valid = false` when
`BCryptDestroyHash`, `BCryptCloseAlgorithmProvider`, or `HeapFree` fails, then
returns an empty digest without returning the failed resource identities.
The caller can refuse launch, but cannot prove or retry cleanup of those native
hash resources. A retained file pin alone does not close this ownership gap.

The RAW stream now uses a separate retained V2 hash/pin bundle. It preserves
the opened file HANDLE, failed CNG hash/algorithm identities, and failed heap
releases in the existing managed PTY slot. Hash release precedes algorithm and
buffer release. This source repair is NOT_RUN and does not qualify the inherited
V1 hash helper's internal cleanup or change its behavior.

Required V1 follow-up: adopt an owner-bearing retained hash ledger without
changing its legacy API silently. V2's source repair still requires actual
fault fixtures for each failed native release, including UTF-16 path cleanup.
The V2 scan now caps producer files at 256 MiB and samples live admission time
around each bounded read. Never infer cleanup from an empty digest.
