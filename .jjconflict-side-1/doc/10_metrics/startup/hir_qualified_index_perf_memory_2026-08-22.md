# HIR qualified-index performance and memory evidence — 2026-08-22

## Verdict

The measured Pure-Simple `SymbolTable` qualified lookup was linear in table
size and retained functional-array copies while binding. A scalar chained hash
index with exact collision checks changes lookup to O(1) average and binding to
O(n) total without changing id-zero, missing, duplicate-first-write, or reset
behavior.

This is **seed-hosted diagnostic evidence**, not Stage 4 admission. The
worktree had no self-hosted executable or provenance receipt. The only runnable
compiler was frozen before measurement:

- source revision: `3d6987adef8a6dba7e354a7c03d672803e67f081`
- executable: `build/startup_perf_memory/toolchains/simple-seed`
- SHA-256: `e5f12c93e87486eb121ca0da837676f9306494e03982bb30566b126a1b7187b4`
- size: 60,403,816 bytes
- identity: `Simple Language v1.0.0-RC`, self-reported Rust bootstrap seed
- host: Linux 6.8.0-137-generic x86_64, AMD Ryzen Threadripper 1950X
- load average near final sample: 25.09 / 26.66 / 26.83

## Measurement contract

All process lanes use N=7. `cold` means a fresh logical cache/home and unique
source or artifact path where applicable; kernel page cache is uncontrolled.
`warm` means one dropped warmup followed by seven launches with a stable path
and logical cache. p95 is nearest rank. `/usr/bin/time -f %M` supplies maximum
RSS. Every lane checks exit status and output; MCP additionally parses two
Content-Length frames, checks ids `1` and `2`, and requires a nonempty tool
list. Its response SHA-256 was stable before and after:
`1a260e77d278ecfaf3f87ee5078c5e767f34843136e345a47bbb522c1a012271`.

The compiler row changes its output path per sample, so its stdout digest is
not expected to match; success and a nonempty SMF artifact are its retained
contract. Raw samples and stderr are under `build/startup_perf_memory/`.

## Executable/mode baseline

| lane | actual mode | cold p50/p95 ms | warm p50/p95 ms | max RSS KiB | parity |
|---|---|---:|---:|---:|---|
| Simple source | Rust-seed-hosted interpreter | 336.853 / 699.187 | 206.117 / 769.895 | 21,504 | pass |
| Simple SMF | Rust-seed SMF loader | 53.977 / 326.433 | 67.863 / 388.169 | 15,616 | pass |
| Simple source-to-SMF | Rust seed compiler | 69.321 / 719.896 | 70.476 / 624.969 | 29,952 | pass |
| Simple MCP initialize + tools/list | Pure-Simple server source, Rust-seed interpreter | 2,155.364 / 3,949.168 | 2,137.622 / 3,099.523 | 130,920 | pass |

Large p95s reflect the shared host and make this an envelope, not a clean-room
release baseline.

## Fair no-op startup context

The available repository harness supports no-output/no-op fixtures for these
installed toolchains: Go 1.22.2, Rust 1.91.1, Python 3.12.3, OpenJDK 21.0.11,
and Bun 1.3.11. All rows use identical no-output semantics, but compiled
native programs, VMs, and script runtimes have different deployment models.
They are context targets rather than proof of implementation equivalence.

| lane | cold p50/p95 ms | warm p50/p95 ms | max RSS KiB | output parity |
|---|---:|---:|---:|---|
| Go native | 7.423 / 11.771 | 6.453 / 9.611 | 1,280 | pass |
| Rust native | 5.549 / 6.248 | 4.745 / 5.059 | 1,792 | pass |
| Python interpreter | 42.599 / 49.744 | 43.100 / 48.541 | 10,496 | pass |
| Java VM, precompiled class | 82.661 / 91.404 | 99.670 / 113.228 | 45,568 | pass |
| Bun runtime | 31.019 / 71.942 | 30.406 / 31.370 | 28,672 | pass |

The repo's broad cross-language harness was not run because it correctly
requires admitted Stage 3/4 provenance. `check-mcp-script-mode-perf.shs` was
also rejected as comparative evidence: its Python/Bun peers are toy servers
with a different tool set, and it records neither p95 nor RSS.

## Dominant defect and change

`SymbolTable.bind_qualified_{type,function}` scanned every retained entry before
insertion, and `lookup_qualified_{type,function}_raw` scanned every entry for
every hit or miss. The real compiler profile records 7,522 qualified-type
queries and 5,832 misses in the dominant HIR import route.

The new route uses two lazy 256-head scalar indexes, parallel next chains, and
exact module/member checks. It hashes each text directly with `char_code_at`,
so no temporary byte array or concatenated qualified key is allocated per
query. The legacy dictionaries remain bind-time compatibility state; staged
lookup never crosses their Dict/Optional boundary. In-place pushes remove the
old functional-array copy on every bind.

Memory cost is bounded and lazy: zero bucket bytes for an unused table; 4,096
head bytes for a table using both function and type indexes; one 8-byte next
slot per retained qualified entry in its corresponding index. This is 12 KiB
less fixed storage per active table than the rejected eager 1,024-head design.

## Before/after Pure-Simple microbenchmark

Command shape: explicit interpreter execution of
`build/startup_perf_memory/qualified_index_bench.spl`. Each row binds both a
qualified type and function per entry, then performs 1,024 hit and miss query
groups. The checksum remained unchanged.

| table entries | bind before/after ms | bind speedup | lookup before/after ms | lookup speedup |
|---:|---:|---:|---:|---:|
| 256 | 546.636 / 117.113 | 4.67x | 8,651.564 / 865.232 | 10.00x |
| 512 | 2,012.643 / 240.318 | 8.37x | 16,971.987 / 960.016 | 17.68x |

Doubling the table changed fixed-query lookup time by 1.962x before and only
1.110x after. Total bind time now changes by 2.052x, consistent with linear
work for twice as many inserts, versus 3.682x before. The final whole-process
maximum RSS was 42,128 KiB; baseline microbenchmark RSS was not captured, so no
microbenchmark memory reduction is claimed.

The deterministic unit probe performs 10,000 lookups in a 4,096-entry table
and requires fewer than 300,000 exact comparisons. It also exercises a real
hash collision, id zero, duplicate-first-write, missing values, reset, and
rebind. Result: 6/6 examples passed.

## End-to-end support and limitations

After the change the real MCP source lane measured cold 1,323.236/1,672.934 ms
and warm 1,057.338/1,507.106 ms, with 130,928/130,812 KiB maximum RSS and exact
response parity. The apparent latency improvement is **supportive only**:
Pure-Simple HIR code is not the Rust seed's compiler implementation, and the
second measurement benefits from warmer kernel page cache. It is not used as
the causal acceptance proof. RSS changed by +8 KiB cold and +600 KiB warm,
within shared-host noise; no aggregate MCP memory improvement is claimed.

Acceptance rests on the direct Pure-Simple microbenchmark, deterministic
comparison-count spec, output parity, and code inspection. Production startup,
compiler, loader, and MCP claims remain pending an admitted source-matched
Stage 3/4 executable.
