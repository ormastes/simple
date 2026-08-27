# SimpleOS QEMU host-WAV evidence extension

Status: AArch64/RISC-V VirtIO-sound host-WAV playback evidence implemented;
x86_64 producers and independent capture evidence remain out of scope.

## Audit result

`scripts/check/check-simpleos-io-audio-qemu.shs --live` validates four retained
serial logs but does not launch QEMU. The only discovered live producer,
`scripts/check/check-simpleos-virtio-snd-qemu.shs`, supports AArch64 and RISC-V
and launches QEMU with `-audiodev driver=none,id=audio0`. Consequently, the
current `SIMPLEOS_AUDIO_PLAYBACK non_silent=1` assertion is guest-authored
semantic evidence, not independent host observation of PCM output. No producer
for `x86_64-virtio-snd.serial.log` or `x86_64-hda.serial.log` was found.

The installed QEMU advertises the WAV backend contract as:

```text
-audiodev wav,id=id[,prop[=value][,...]]
    path= path of wav file to record
```

## Smallest architecture-consistent extension

1. Extend `check-simpleos-virtio-snd-qemu.shs` only at the host evidence edge:
   replace the discard backend with a per-run path under the existing evidence
   directory, for example `-audiodev wav,id=audio0,path=<row>.playback.wav`.
   Pin `out.fixed-settings`, frequency, channels, and sample format to the
   deterministic guest scene rather than relying on host defaults.
2. After QEMU exits, fail closed unless the path is a new regular file with a
   valid RIFF/WAVE header, supported PCM format, nonzero data frames, and at
   least one nonzero sample. Record file SHA-256, byte count, frame count,
   channels, frequency, sample format, QEMU path/version, kernel SHA-256, and
   source-set SHA-256 in a sibling evidence record.
3. Bind the central checker row to both the serial receipt and sibling WAV
   record. A missing, stale, symlinked, truncated, silent, hash-mismatched, or
   provenance-mismatched WAV must fail. Add self-test fixtures for one admitted
   WAV and each rejection class.
4. Treat WAV as playback evidence only. QEMU's WAV backend does not prove
   microphone/capture input; retain capture as a separate guest/device receipt
   until an independent host-fed capture fixture is designed.
5. Add x86_64 VirtIO-sound and HDA launch owners separately before the aggregate
   four-row `--live` result can be self-producing. Do not relabel AArch64 or
   RISC-V WAV output as x86 evidence.

## Acceptance

- Each live VirtIO row has one fresh serial log, one fresh host-created WAV,
  and one provenance record bound by hashes.
- The deterministic playback receipt and WAV metadata agree on format and
  frame count; any resampling allowance is explicit and tested.
- Host-observed non-silence comes from parsed WAV sample bytes, never from the
  guest's `non_silent=1` marker alone.
- Aggregate PASS remains blocked until independent x86_64 VirtIO-sound and HDA
  producers meet the same evidence contract.

## Implemented result

`check-simpleos-virtio-snd-qemu.shs` now records a fresh per-row WAV through
QEMU's pinned PCM16 stereo 48 kHz backend, rejects malformed, silent, symlinked,
or stale output, and binds its hashes to the kernel, source set, and QEMU
identity. Its non-QEMU self-test covers valid, silent, truncated, symlink, and
stale fixtures. The aggregate checker requires this evidence for AArch64 and
RISC-V only and emits `capture_claim=none`.
