# Linux group observation receipts omit native allocation failure

- ID: `linux_group_observation_nullable_receipt_2026_11_14`
- Severity: P2
- Status: fix-implemented-verification-pending; source review pending, runtime NOT_RUN.
- Base: `d2d6a695724b8e3645b3b6e73127fba0b0caaff4`.
- Owner: `src/lib/nogc_sync_mut/io/linux_process_owner.spl`.

## Proven source failure

`rt_linux_group_collected_stream_v2` in `runtime_linux_group_owner_impl.h`
calls `rt_lg_observation`, which allocates through `owned_adapter_values` in
`runtime_process_owned.c`. That allocator returns NULL if `rt_array_new` or
`rt_array_push` fails; it frees only the incomplete receipt array. The
non-Linux `group_stream_unavailable_v2` also returns NULL on allocation/push
failure. The former Simple extern promised nonoptional `[i64]` and forwarded
the result directly into `linux_process_poll_decode_v1`, whose first operation
is `.len()`.

The same real allocation boundary exists for `rt_linux_group_poll_v1` and
`rt_linux_group_collect_v1`. All three declarations and call sites are repaired
together. No C signatures or return pointer widths change.

## Native ownership and recovery

The collected-stream projection performs no poll, wait, native cleanup, lease
transfer or owner mutation. An allocation failure leaves the actual native
owner and collected evidence intact. `owned_adapter_values` frees only its
failed result array. Poll can refresh native observations before allocation;
collection can complete native cleanup and set `rt_linux_group.collected = 1`
before allocation. A missing receipt therefore cannot mean no native effect.

`native_linux_group_finish_stream_v2` in
`src/app/bootstrap_builder/native_group_linux_broker.spl` retains the same
`LinuxProcessLeaseV1`: it first asks for the immutable collected projection,
then attempts collection on an error, records errors and retries. A later
projection can recover the actual collected evidence. This repair adds no
new native call or retry and changes no publication/release authority.

## Repair and acceptance criteria

REQ-COLLECTION-NULL-001: declare the three allocating observation returns as
`[i64]?`; route all three through production
`linux_process_observation_decode_v2`. None returns
`Linux process observation receipt unavailable; lease retained`, without
inventing exit, native absence, cleanup, empty arrays or success.

REQ-COLLECTION-NULL-002: Some delegates to the original decoder, preserving
status errors, array shape, bounds, terminal reap checks and successful facts.
No-child cleanup remains on its separate native classification path. Invalid
or unsupported statuses remain errors distinct from allocation absence.

Seven authored decoder cases cover absence, malformed arrays, unsupported and
invalid statuses, incomplete reap, invalid memory bounds, complete facts and
nonterminal facts. Source/manual pair:
`test/01_unit/lib/nogc_sync_mut/io/linux_process_collection_nullable_v2_spec.spl`
and its mirrored manual under `doc/06_spec/01_unit/lib/nogc_sync_mut/io/`.

## Qualification and separate checker limitation

All runtime specs, doc generation, allocation-failure injection, native broker
recovery integration, compiler/core/MCP checks, mapping and ABI compilation
remain **NOT_RUN** in this source-only session. No admitted runtime is available;
the prior bounded native campaign is closed. No seed, bootstrap or native build
was attempted. Pure decoder inputs exercise the actual production adapter but
do not qualify emitted optional-array ABI or native OOM behavior.

The retained pointer-map log `/tmp/windows-journal-pointer-map-20261114.log`
has five separate INPUT_REF_ARGS arity false positives: the macro expands six
parameters but the parser counts one. Its null classifier also treats the
nested scalar `? 0 : EINVAL` inside a return-call argument as a direct null
return. Those checker defects are outside this repair; no checker, baseline or
guard changes are included. The real nullable allocator chain independently
establishes this bug.

## Source evidence SHA-256

These unchanged source hashes bind the ownership analysis:

| Source | SHA-256 |
|---|---|
| `src/runtime/runtime_linux_group_owner_impl.h` | `d158452683d543a2fd3eebe514dbc1545c3a437d0564557ef08419f2c6be8d3e` |
| `src/runtime/runtime_process_owned.c` | `00d367fe5eae245fa22cb6b555178224d36b31cbbec2a35a1d308cd9b7914698` |
| `src/app/bootstrap_builder/native_group_linux_broker.spl` | `43a20a251c08eb609d3a655dca5cb2878856e96a4b1425014c0fb2eec5484b52` |
| `scripts/check/check-rt-pointer-ref-map.py` | `88a4f449144891a99698ca770c5af1779b9a4e724c6b1f389418f2649fc515d5` |

Final changed-source and complete review-bundle hashes are supplied separately
to the reviewer, avoiding a self-referential document hash.
