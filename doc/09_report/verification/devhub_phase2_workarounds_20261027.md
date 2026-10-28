# DevHub phase-2 application repairs and tracked workarounds

User direction: keep the existing phase-2 compiler, use Astra guidance/review and parallel work, land independent fixes first, and keep Messenger database access an active required feature. Sol and Terra supplied the database pre-research. This report does not claim complete DevHub or SSpec qualification.

## Producer and actual passing evidence

The existing producer is `C:/dev/simple-disk-headroom-warm-bootstrap-storage-20261025/output/stage3/simple.exe`, SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. Despite its directory name it is phase 2. It was not rebuilt. Application fixtures used LLVM and the real core-C runtime, with the existing real memory-headroom object supplied explicitly because this producer's runtime roster predates it.

| Focused production check | Actual result | Artifact SHA256 |
|---|---|---|
| RFC header case/body separation | Bash red exit1, then green exit0; three groups | See the checked-in production probe and local evidence |
| GH JSON decoded string/control round trip | Native P2 red exit1, green exit0 | `14decf3e075a994cf10dd98add7f18b45f46f9f48b7660fdf1af4155c5f512bc` |
| Windows private atomic replacement | Actual C provider red exit1, green exit0, final owner/System DACL | `e13b9778a85b6cb23184e515f52a8b9a6e2c6d14dfbd1e6a960d3b4fd9e4461d` |
| History selection, ordering, ties and invalid metadata | Native P2 compile0/run0 | `926cd8fb6d22c5ab6ca0ab929889a5070cf2f8fb1095bbbb8e7bd8bdadfc6044` |
| Flags, MinIO expiry and JSON values | Native P2 compile0/run0 | `5ac5ddf12ba7a6982c338063edc1eee3cf6e65a1811ba3e2cd295a770a4665c8` |
| Actual private auth persistence | Native P2 compile0/run0, escaped Unicode/dotted providers/injection/refusal/deletion | `720834f8a0c613e0401802df257dcb8813f0c3329bcbe2b9d509aa05d1852f02` |
| Actual editor files | Native P2 compile0/run0, Unicode/empty/unique/refusal/cleanup | `5f7e4f4da734fb08eb527187d868541f83195847e746611155529634e755284c` |
| Actual Outlook/OAuth caches and Graph guards | Native P2 compile0/run0 after decimal permission-mode workaround; seven groups | `e285b95b2f4250817eec5555aee4d67fea0f1f299d2d3d3568381ae8f9b044fd` |
| Canonical bug API append on a copy | Native P2 compile0/run0; unsigned CRC known answers; independent zlib and exact original-body preservation | `4e7a0160881d43b5bf54df41b628c5c6ddc5651cb664658494705314f1849b18` |
| Private curl HTTP transport | Native P2 compile0/run0; six exact requests, form/UTF-8, redirect refusal, empty GET, size refusal, measured 30.054s timeout, staging cleanup | `4b3dd930128c9cf6006c0ded17a535a3bce4af77ce13a4c27592b2998b95e052` |
| Signed binary MinIO upload | Native P2 compile0/run0; independent exact octets, payload hashes, SigV4, dot-segment path, zero-byte file and missing-file request count | `3ec2fb24ebead331d4e50e8f68fce54cbd7ba4c49c1e0600b9126499dc8c3247` |

The registry copy retained all 5265 original rows across six tables, including 20 opaque overwide legacy rows. Removing only the 32 newly inserted row lines reproduced the original payload byte for byte. Duplicate-ID, corrupt-CRC and pending-WAL cases each exited1 without changing input. After syncing release commit `16b7917a2349bb103035326d4883152a2c14177d`, the qualified API registered eight open records in the actual registry. Independent audit preserved all 5267 existing rows and all 20 opaque rows exactly; 32 new rows were inserted. The final unsigned CRC is 3989747835 and the registry SHA256 is `de927717baac960d519afd5c2677a5cbbffc575cc4ff5e0f8714eeca793c2846`. No registry cell or checksum was manually edited. See `devhub_workaround_registration_20261027.md`.

## Coded behavior

Production consumers use real configured file providers, checked failure paths and private atomic secret files. OAuth constructs and sends a form request, uses decoded JSON token values, and delegates Windows transport to the private-file curl owner. Both Graph adapters validate pagination URL, cycle, page limit and response shape. Daily-debug captures its watermark before fetching, aborts on errors or missing source configuration, and avoids cache writes in dry-run mode. Editor and pager no longer share predictable temporary files. MinIO preserves binary bodies, uses strict expiry validation and canonical JSON, and returns failure for unhealthy JSON output. Missing provider facade exports are supplied without globally changing selected GC/concurrency family.

The Windows atomic file provider applies a protected owner/System DACL before any secret bytes are written. The missing Rust mode twin and collision cleanup ownership are coded; Rust runtime verification remains unqualified after the bounded test attempts, including a corrected test import error. Do not describe the C result as Rust parity evidence.

The decimal masks preserve exact permissions: 384=0600 and 448=0700. An earlier native cache run wrote read-only target and staging files with the octal source form; the staging file contained the correct new value. Replacing the mode carrier with its decimal equivalent made the unchanged regression pass. The exact compiler-lowering cause remains open.

## Qualification limits and remaining DB work

The bounded native-process bridge and curl HTTP/binary-upload loopback checks passed against the unchanged phase-2 producer. Independent servers verified exact requests and bytes rather than trusting only process output. Earlier curl attempts returned the observed prelaunch tuple (empty stdout, missing command, exit-1) without a request. The compatibility path retains the normal process API first and permits one bounded native fallback for only that signature. It does not retry arbitrary transport or HTTP errors.

Formal modern SSpec scenarios are authored but unexecuted, and spipe-docgen has not reported zero stubs. Existing pinned-producer matcher, nested callback and environment tuple failures remain tooling/product compatibility defects, not external infrastructure. The runtime-family matrix and live Microsoft/provider account exchange are not claimed qualified.

Messenger database access remains required and unresolved. Its old production-adapter RTS01 panic is not fixed by the independent history-selector result. The selector bounds retained rows, not whole-database I/O. Follow `doc/05_design/devhub_secured_sqlite_phase2_solution_20261027.md` for the Sol/Terra research and Astra solution. Do not rerun the capped unchanged fixture or silently reset its cycle count.

All 30 new workaround markers were applied after canonical API registration and audited to immediately precede code and reference registered records. The final exact commit receives Astra review. The original source-fix commit is `16296fd91449d482797d4b6f42c810cdea716157`; base sync commit `842d92702049268524a39e4d11d937e4106da6d4` retained those changes. Upstream runtime overlaps only added exclusive no-follow copy/link providers; they did not change the qualified atomic-write or process tuple contracts. Comment-only tagging did not change the previously qualified implementations. Never hand-edit or regenerate the derived `.simple/workarounds.sdn` index or truncate legacy bug rows.
