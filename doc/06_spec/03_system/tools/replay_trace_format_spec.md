# Replay trace format specification

Status: **cycle one 30 PASS / 3 FAIL; cycle two 1 PASS / 2 FAIL; cycle three 2 PASS / 0 FAIL**. Cycle one executed all 33 cases in 763 ms, exit 1. All three new codec cases failed before field assertions with `method 'to_i32' not found on value of type str in nested call context`. This result reproduces a producer dispatch gap, not yet the discarded-field defect. Baseline log/resource receipts are under `build/phase-one-storage-gui-diagnostic/replay_trace_format_spec/cycle-one.*`; the manifest is `trace-format-cycle-one-inputs.sdn`. Peak RSS was 218276 KiB, enforced limit 5859375 KiB, quiescent=1.

The producer's ordinary string dispatcher accepts `to_i32`, while its nested text dispatcher omits that alias. The cycle-two compatibility change altered only the two affected assignments to `to_i64() as i32`. This is an explicitly recorded accommodation, not a compiler repair or a claim that the original method call was invalid. See `doc/08_tracking/bug/replay_manifest_nested_integer_conversion_2026-10-11.md`. Valid numeric fields preserve their intended conversion; malformed numbers and narrowing overflow remain unqualified. Cycle-two owner SHA-256: `f280ec94eb123d5a301ba345d11414d0d7eb475e2edb93787c81250127946ad2`.

Cycle two selected only original failed cases 31–33. It reported **1 PASS / 2 FAIL, 356 ms, exit 1**: the default roundtrip passed, and populated/reordered manifests reached the unchanged field assertions but returned timestamp zero instead of 1700000001 and 987654321. Evidence is `build/phase-one-storage-gui-diagnostic/replay-trace-manifest-cycle-two_spec/cycle-two.log`, sibling resource/exit receipts and `trace-format-cycle-two-inputs.sdn`. Peak RSS was 243048 KiB, enforced limit 5859375 KiB, quiescent=1.

The tested repair restores all four serialized fields: magic, byte order, explicit pointer width and timestamp. Absent fields retain prior defaults, including deriving pointer width from architecture when omitted. Existing valid numeric conversions and shell persistence are unchanged. Tested final owner SHA-256: `475982cd41f186ed33e0a4146905d60d059ef93ea59e4e36816e006fdc190d29`. The source defect is recorded separately in `doc/08_tracking/bug/replay_manifest_dropped_metadata_2026-10-11.md`; the producer alias issue remains unresolved.

Final cycle three passed **2/2, 275 ms, exit 0**. `build/phase-one-storage-gui-diagnostic/replay-trace-manifest-fields-cycle-three_spec.spl` selected only original cases 32–33, retaining every assertion and the helper/imports, with adjacent SDN mapping. Evidence is in the sibling `replay-trace-manifest-fields-cycle-three_spec/cycle-three.log` and resource/exit receipts. Peak RSS was 236460 KiB, enforced limit 5859375 KiB, quiescent=1. The coordinator matched all nine inputs in `trace-format-cycle-three-inputs.sdn` before and after execution. Neither the original 30 greens nor newly green case 31 reran. All three allowed cycles are now consumed; these results span successive source snapshots, and no complete repaired-source 33-case pass is claimed.

The production route is `TracePackage.read_manifest` -> existing shell read/error handling -> `TraceManifest.from_sdn`. Tests call the same production text decoder and real `TraceManifest.to_sdn`, rather than substituting a test parser or touching files. `adapters/test_runner_replay.spl` continues to consume `TracePackage.read_manifest`.

## Extraction and known gap

Before baseline, the parser body moved unchanged from `TracePackage.read_manifest` to `TraceManifest.from_sdn(source)`. Its bytes and statement order are identical after the sole expression substitution `cat_result.stdout.split` -> `source.split`. Defaults, branch order, string replacements, numeric conversion, constructor and returned Result remain unchanged. The persisted reader retains its original shell command and error branch, then delegates. The normalized body hashes and original/extracted owner hashes are recorded in `build/phase-one-storage-gui-diagnostic/trace-manifest-decoder-extraction.sdn`; the exact production diff is beside it as `trace-manifest-decoder-extraction.patch`.

Before the final repair, the decoder reconstructed `magic`, `pointer_bits`, `endian` and `created_at` from constructor defaults instead of recovering their serialized values. Cycle two reproduced the lost timestamps, and the tested repair restores these fields. Case 32 distinguishes explicit pointer width, byte order and timestamp; case 33 independently distinguishes byte order and timestamp using literal SDN. Case 31 verifies all nine ordinary default fields. The model currently accepts explicit target fields without architecture/ABI consistency checks; case 32 verifies field preservation, not acceptance of an executable target configuration. All codec fixtures use magic `SRPL`; the new magic assignment lacks a distinct-value oracle. Malformed-schema validation and arbitrary string escaping are separate open obligations.

Extracted production owner SHA-256: `4d7356e1f950406bc72242178823b3b7b1ecbfe2949779a243b00ada6b55e965`.
Canonical spec SHA-256: `f318485ed906bb40b2d94172a282ebaead1b7294e63139692d8e8d4ccd959a1c`.

## Evidence scope and remaining obligations

These are in-memory format/index diagnostics. Existing shell-backed manifest, checkpoint and event persistence is unchanged and unverified. Its filesystem-neutral SOSIX routing, durable writes, I/O error handling, native/self-hosted checks, whole-Phase1 admission and measured coverage are not established by this codec baseline. The filesystem owner confirmed this decoder lane has no ownership overlap; filesystem integration remains open. No new filesystem bypass, FFI or JSON format is introduced.

`@cover` 80% is an admission target, not measured coverage. The manual is synchronized directly to the executable source below; SPipe docgen is pending. Production imports remain `std.nogc_sync_mut.io.process_ops.{shell}` and `std.nogc_sync_mut.replay.types.{Arch, Endian, TargetDesc}`. The spec adds no generic SDN parser dependency.

Requirement trace: `REQ-SSPEC-SYSTEM`. The original canonical and legacy `test/system/replay_trace_format_spec.spl` were byte-identical, SHA-256 `b74c4c25e30d2de2c72ffb92e42108ed37a0eca91705d502e1aefa7bdc7b66cd`; removal of the duplicate preserves all 30 scenarios and loses no legacy requirement or tag.

The baseline selected all 33 scenarios once. The cycle-two derivative retained the three baseline failures; the final derivative retains only the two remaining failures. Both preserve the exact prefix/imports/helper and use original case numbers and SHA mapping in SDN; passing cases are excluded.

## Scenarios and visible steps

Each scenario contains a visible `step(...)`. The three new scenarios separate input creation/serialization from production decoding and field inspection. Result failures explicitly fail the scenario; successful decoding checks all nine fields through a shared assertion helper.

| Case | Scenario | Evidence |
|---|---|---|
| 1 | create sets magic to SRPL | Baseline PASS; not rerun |
| 2 | create sets version to 1 | Baseline PASS; not rerun |
| 3 | create stores arch text | Baseline PASS; not rerun |
| 4 | create stores replay_mode | Baseline PASS; not rerun |
| 5 | create sets pointer_bits from arch | Baseline PASS; not rerun |
| 6 | x86_64 has 64 pointer_bits | Baseline PASS; not rerun |
| 7 | create sets event_count to 0 | Baseline PASS; not rerun |
| 8 | create sets checkpoint_count to 0 | Baseline PASS; not rerun |
| 9 | create sets endian to little | Baseline PASS; not rerun |
| 10 | to_sdn contains SRPL | Baseline PASS; not rerun |
| 11 | to_sdn contains arch | Baseline PASS; not rerun |
| 12 | to_sdn contains replay mode | Baseline PASS; not rerun |
| 13 | create stores key | Baseline PASS; not rerun |
| 14 | create stores event_id | Baseline PASS; not rerun |
| 15 | create stores kind | Baseline PASS; not rerun |
| 16 | create starts empty | Baseline PASS; not rerun |
| 17 | add increments entry_count | Baseline PASS; not rerun |
| 18 | lookup returns matching entries | Baseline PASS; not rerun |
| 19 | lookup returns empty for missing key | Baseline PASS; not rerun |
| 20 | create sets base_dir | Baseline PASS; not rerun |
| 21 | create manifest has correct arch | Baseline PASS; not rerun |
| 22 | create manifest has correct mode | Baseline PASS; not rerun |
| 23 | event_count starts at 0 | Baseline PASS; not rerun |
| 24 | list_checkpoints starts empty | Baseline PASS; not rerun |
| 25 | summary contains arch | Baseline PASS; not rerun |
| 26 | summary contains mode | Baseline PASS; not rerun |
| 27 | summary contains TracePackage header | Baseline PASS; not rerun |
| 28 | summary contains base_dir | Baseline PASS; not rerun |
| 29 | create with all 6 modes — semantic | Baseline PASS; not rerun |
| 30 | create with all 6 modes — vm | Baseline PASS; not rerun |
| 31 | round-trips every default manifest field through SDN | Cycle-two PASS; not rerun |
| 32 | preserves explicit target metadata and nonzero statistics through SDN | Cycle-three selected PASS |
| 33 | decodes reordered literal SDN metadata without the encoder as its oracle | Cycle-three selected PASS |

<details>
<summary>Exact executable SSpec source</summary>

```simple
# codex-system-test
# @req REQ-SSPEC-SYSTEM
# @cover src/lib/nogc_sync_mut/replay/trace_format.spl 80%
# Coverage percentage is an admission target, not measured coverage.
# @tag:system
# Pure manifest/index diagnostics. Shell persistence and neutral SOSIX routing remain unverified.

use std.spec.{describe, it, expect, fail, step}
use std.nogc_sync_mut.replay.trace_format.{TraceManifest, TraceIndexEntry, TraceIndex, TracePackage}

fn expect_manifest_fields(actual: TraceManifest, expected: TraceManifest):
    expect(actual.magic).to_equal(expected.magic)
    expect(actual.version).to_equal(expected.version)
    expect(actual.arch).to_equal(expected.arch)
    expect(actual.pointer_bits).to_equal(expected.pointer_bits)
    expect(actual.endian).to_equal(expected.endian)
    expect(actual.replay_mode).to_equal(expected.replay_mode)
    expect(actual.event_count).to_equal(expected.event_count)
    expect(actual.checkpoint_count).to_equal(expected.checkpoint_count)
    expect(actual.created_at).to_equal(expected.created_at)

# ============================================================================
# TraceManifest
# ============================================================================

describe "TraceManifest":
    it "create sets magic to SRPL":
        step("create sets magic to SRPL")
        val m = TraceManifest.create("x86_64", "qemu")
        expect(m.magic).to_equal("SRPL")

    it "create sets version to 1":
        step("create sets version to 1")
        val m = TraceManifest.create("riscv32", "kernel")
        expect(m.version).to_equal(1)

    it "create stores arch text":
        step("create stores arch text")
        val m = TraceManifest.create("riscv32", "qemu")
        expect(m.arch).to_equal("riscv32")

    it "create stores replay_mode":
        step("create stores replay_mode")
        val m = TraceManifest.create("x86_64", "process")
        expect(m.replay_mode).to_equal("process")

    it "create sets pointer_bits from arch":
        step("create sets pointer_bits from arch")
        val m = TraceManifest.create("riscv32", "qemu")
        expect(m.pointer_bits).to_equal(32)

    it "x86_64 has 64 pointer_bits":
        step("x86_64 has 64 pointer_bits")
        val m = TraceManifest.create("x86_64", "qemu")
        expect(m.pointer_bits).to_equal(64)

    it "create sets event_count to 0":
        step("create sets event_count to 0")
        val m = TraceManifest.create("x86_64", "qemu")
        expect(m.event_count).to_equal(0)

    it "create sets checkpoint_count to 0":
        step("create sets checkpoint_count to 0")
        val m = TraceManifest.create("x86_64", "qemu")
        expect(m.checkpoint_count).to_equal(0)

    it "create sets endian to little":
        step("create sets endian to little")
        val m = TraceManifest.create("x86_64", "qemu")
        expect(m.endian).to_equal("little")

    it "to_sdn contains SRPL":
        step("to_sdn contains SRPL")
        val m = TraceManifest.create("x86_64", "qemu")
        val sdn = m.to_sdn()
        expect(sdn).to_contain("SRPL")

    it "to_sdn contains arch":
        step("to_sdn contains arch")
        val m = TraceManifest.create("riscv32", "kernel")
        val sdn = m.to_sdn()
        expect(sdn).to_contain("riscv32")

    it "to_sdn contains replay mode":
        step("to_sdn contains replay mode")
        val m = TraceManifest.create("x86_64", "semantic")
        val sdn = m.to_sdn()
        expect(sdn).to_contain("semantic")

# ============================================================================
# TraceIndexEntry
# ============================================================================

describe "TraceIndexEntry":
    it "create stores key":
        step("create stores key")
        val e = TraceIndexEntry.create(4096, 10, "memory_write")
        expect(e.key).to_equal(4096)

    it "create stores event_id":
        step("create stores event_id")
        val e = TraceIndexEntry.create(100, 42, "source_line")
        expect(e.event_id).to_equal(42)

    it "create stores kind":
        step("create stores kind")
        val e = TraceIndexEntry.create(0, 0, "schedule")
        expect(e.kind).to_equal("schedule")

# ============================================================================
# TraceIndex
# ============================================================================

describe "TraceIndex":
    it "create starts empty":
        step("create starts empty")
        val idx = TraceIndex.create()
        expect(idx.entry_count).to_equal(0)

    it "add increments entry_count":
        step("add increments entry_count")
        var idx = TraceIndex.create()
        val e = TraceIndexEntry.create(100, 1, "memory_write")
        idx.add(e)
        expect(idx.entry_count).to_equal(1)

    it "lookup returns matching entries":
        step("lookup returns matching entries")
        var idx = TraceIndex.create()
        idx.add(TraceIndexEntry.create(100, 1, "memory_write"))
        idx.add(TraceIndexEntry.create(200, 2, "source_line"))
        idx.add(TraceIndexEntry.create(100, 3, "memory_write"))
        val found = idx.lookup(100)
        expect(found.len()).to_equal(2)

    it "lookup returns empty for missing key":
        step("lookup returns empty for missing key")
        var idx = TraceIndex.create()
        idx.add(TraceIndexEntry.create(100, 1, "memory_write"))
        val found = idx.lookup(999)
        expect(found.len()).to_equal(0)

# ============================================================================
# TracePackage
# ============================================================================

describe "TracePackage":
    it "create sets base_dir":
        step("create sets base_dir")
        val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
        expect(pkg.base_dir).to_equal("/tmp/test_trace")

    it "create manifest has correct arch":
        step("create manifest has correct arch")
        val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
        expect(pkg.manifest.arch).to_equal("riscv32")

    it "create manifest has correct mode":
        step("create manifest has correct mode")
        val pkg = TracePackage.create("/tmp/test_trace", "process", "x86_64")
        expect(pkg.manifest.replay_mode).to_equal("process")

    it "event_count starts at 0":
        step("event_count starts at 0")
        val pkg = TracePackage.create("/tmp/test_trace", "kernel", "aarch64")
        expect(pkg.event_count()).to_equal(0)

    it "list_checkpoints starts empty":
        step("list_checkpoints starts empty")
        val pkg = TracePackage.create("/tmp/test_trace", "qemu", "x86_64")
        val cps = pkg.list_checkpoints()
        expect(cps.len()).to_equal(0)

    it "summary contains arch":
        step("summary contains arch")
        val pkg = TracePackage.create("/tmp/test_trace", "qemu", "riscv32")
        val s = pkg.summary()
        expect(s).to_contain("riscv32")

    it "summary contains mode":
        step("summary contains mode")
        val pkg = TracePackage.create("/tmp/test_trace", "container", "x86_64")
        val s = pkg.summary()
        expect(s).to_contain("container")

    it "summary contains TracePackage header":
        step("summary contains TracePackage header")
        val pkg = TracePackage.create("/tmp/test_trace", "vm", "riscv64")
        val s = pkg.summary()
        expect(s).to_contain("TracePackage:")

    it "summary contains base_dir":
        step("summary contains base_dir")
        val pkg = TracePackage.create("/tmp/my_trace", "semantic", "arm32")
        val s = pkg.summary()
        expect(s).to_contain("/tmp/my_trace")

    it "create with all 6 modes — semantic":
        step("create with all 6 modes — semantic")
        val pkg = TracePackage.create("/tmp/t", "semantic", "x86_64")
        expect(pkg.manifest.replay_mode).to_equal("semantic")

    it "create with all 6 modes — vm":
        step("create with all 6 modes — vm")
        val pkg = TracePackage.create("/tmp/t", "vm", "x86_64")
        expect(pkg.manifest.replay_mode).to_equal("vm")

describe "TraceManifest production text codec":
    it "round-trips every default manifest field through SDN":
        step("Serialize a real 32-bit kernel manifest")
        val expected = TraceManifest.create("riscv32", "kernel")
        val serialized = expected.to_sdn()

        step("Decode using the production reader and inspect all nine fields")
        match TraceManifest.from_sdn(serialized):
            Ok(decoded_manifest):
                expect_manifest_fields(decoded_manifest, expected)
            Err(captured_manifest_error):
                fail("Manifest decode failed: {captured_manifest_error}")

    it "preserves explicit target metadata and nonzero statistics through SDN":
        step("Serialize explicit fields accepted by the manifest model")
        var expected = TraceManifest.create("x86_64", "process")
        # Field fidelity is independent of architecture/ABI consistency validation.
        expected.pointer_bits = 32
        expected.endian = "big"
        expected.event_count = 81
        expected.checkpoint_count = 3
        expected.created_at = 1700000001
        val serialized = expected.to_sdn()

        step("Recover the stored fields without reconstructing target defaults")
        match TraceManifest.from_sdn(serialized):
            Ok(decoded_manifest):
                expect_manifest_fields(decoded_manifest, expected)
            Err(captured_manifest_error):
                fail("Manifest decode failed: {captured_manifest_error}")

    it "decodes reordered literal SDN metadata without the encoder as its oracle":
        step("Provide an independent SDN manifest with reordered groups and fields")
        val lines: [text] = [
            "stats:",
            "  created_at: 987654321",
            "  checkpoint_count: 2",
            "  event_count: 13",
            "replay:",
            "  mode: \"vm\"",
            "target:",
            "  endian: \"big\"",
            "  pointer_bits: 64",
            "  arch: \"riscv64\"",
            "trace:",
            "  version: 1",
            "  magic: \"SRPL\"",
            "  format: \"simple-replay-trace\""
        ]
        var expected = TraceManifest.create("riscv64", "vm")
        expected.endian = "big"
        expected.event_count = 13
        expected.checkpoint_count = 2
        expected.created_at = 987654321

        step("Decode the literal input and inspect every recovered field")
        val serialized = lines.join("\n")
        match TraceManifest.from_sdn(serialized):
            Ok(decoded_manifest):
                expect_manifest_fields(decoded_manifest, expected)
            Err(captured_manifest_error):
                fail("Literal manifest decode failed: {captured_manifest_error}")
```

</details>
