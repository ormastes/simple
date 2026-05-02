<!-- codex-research -->
# Hardware Driver Safety And Performance NFR Options

## Option N1: Correctness-first

Description:
Prioritize DMA ownership, address validity, completion correctness, and truthful support labeling before performance tuning.

Pros:
- Lowest regression risk
- Matches the current unstable GPU state

Cons:
- Throughput gains land later

Effort:
S (2-4 files per slice)

## Option N2: Balanced correctness and latency

Description:
Require correctness fixes plus completion-mode selection and measurable reduction of unnecessary copies in the same phase.

Pros:
- Better user-visible progress
- Keeps performance tied to safety work

Cons:
- More code touched per slice

Effort:
M (4-7 files per slice)

## Option N3: Aggressive acceleration

Description:
Prioritize interrupt paths, zero-copy, and acceleration claims quickly, accepting more staged risk.

Pros:
- Fastest path to headline performance features

Cons:
- Not appropriate while `virtio_gpu` is still failing
- Higher regression and debugging cost

Effort:
L (7-10 files per slice)
