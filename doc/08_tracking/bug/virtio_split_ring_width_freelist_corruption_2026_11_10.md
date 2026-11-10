# VirtIO split ring corrupts neighboring fields and reuses live descriptors

Priority: P1. Source fix implemented; runtime verification pending.

Owner: `src/os/drivers/virtio/virtio_common.spl`, `Virtqueue`.
Found while implementing the existing VirtIO-console host-GPU transport gap on
release/1.0.0 baseline `6d496f82c5acabc2fc52b2b78146272e664dc371`.

The baseline uses 32-bit accesses for 16-bit descriptor `next`, available
`idx`, and available-ring entries. A store to descriptor offset 14 overwrites
the low two bytes of the next descriptor address. Publishing an available
index likewise overwrites slot zero, and publishing a slot overwrites its
neighbor. `init_free_list` omits the last descriptor link; zeroed backing
memory therefore sends allocation back to descriptor zero after exhaustion.
The used-ring base is also two bytes off its required four-byte alignment for
normal even queue sizes. Scaling a u16 descriptor index before widening wraps
offsets for indices at or above 4096.

The repair uses halfword MMIO, a final out-of-range free-list sentinel, aligned
used-ring placement, widened address arithmetic, and explicit available-index
wrap. Ring publication and device notification have memory barriers. Invalid
queue geometry is inert; ring flags and indices are initialized before use.

Normative basis: [VirtIO 1.2 split-ring layout](https://docs.oasis-open.org/virtio/virtio/v1.2/virtio-v1.2.html),
section 2.7. Descriptor tables align to 16 bytes, available rings to two, used
rings to four; queue size is a power of two up to 32768.

Verification artifacts:

- `test/01_unit/os/drivers/virtio/virtio_split_ring_spec.spl`: actual queue
  methods through the existing typed MMIO journal; distinguishes halfword
  calls, exhaustion/reuse, a one-element ring, wrapped index, large descriptor
  offset, alignment and invalid geometry.
- `test/fixtures/virtio_split_ring/native_memory.spl`: real DMA-owned host
  allocation and volatile MMIO; checks adjacent descriptor/ring sentinels and
  exact descriptor exhaustion. Every failure returns nonzero. This is host
  memory evidence, not live DMA or QEMU device evidence.

No executable PASS is claimed yet: the campaign has no admitted self-hosted
test runner. Required evidence is a red/green native-memory execution and
focused unit execution with exact producer identity and positive test counts.
The separate VirtIO-console transport remains unavailable until its device,
socket, session, and live x86_64/RISC-V acceptance gates pass.

Source review passed at `d9d3bfec0895b0c8f130373724a8dcd5552f7b96`.
Working/staged environment guards, workspace-root guard, and executable-spec
layout check passed. The user authorized source fixes with executable tests
to land while unavailable runtime checks remain explicitly waiting for
verification; this does not waive an actual failing check or close this bug.
