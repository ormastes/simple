# Domain Research: Browser Net Bundle Optimization

Sources: ZIP APPNOTE 6.3.10, WebP Container Spec, RFC 9113 (HTTP/2), RFC 9000 (QUIC),
RFC 9114 (HTTP/3), Wikipedia Bloom Filter, computed Bloom parameters.

---

## 1. ZIP Archive Format

### Local File Header (streaming-safe, no seek needed)
```
Offset  Size  Field
0       4     Signature: 0x04034b50 ("PK\x03\x04")
4       2     Version needed to extract
6       2     General purpose bit flag (bit 3 = data descriptor follows)
8       2     Compression method: 0=stored, 8=deflate
10      2     Last mod file time
12      2     Last mod file date
14      4     CRC-32
18      4     Compressed size   (0xFFFFFFFF → see ZIP64 extra)
22      4     Uncompressed size (0xFFFFFFFF → see ZIP64 extra)
26      2     File name length
28      2     Extra field length
30      n     File name (UTF-8 if bit 11 set)
30+n    m     Extra field (see ZIP64 extra below)
```

### Data Descriptor (when bit 3 set — streaming write mode)
```
[optional sig 0x08074b50]  4 bytes
CRC-32                     4 bytes
Compressed size            4 bytes (8 bytes for ZIP64)
Uncompressed size          4 bytes (8 bytes for ZIP64)
```

### ZIP64 Extra Field (header id = 0x0001)
```
Header ID   2 bytes  0x0001
Data size   2 bytes
Orig size   8 bytes
Comp size   8 bytes
Offset LH   8 bytes  (central dir only)
Disk #      4 bytes  (central dir only)
```

### Streaming Extraction Algorithm
```
loop:
  read 4 bytes → if == 0x04034b50: parse local header
    skip extra field; stream compressed_size bytes through inflate
    verify CRC32; emit decompressed bytes
  elif == 0x02014b50: central dir start → done
  elif == 0x08074b50: data descriptor (skip 12/20 bytes)
```

### CRC32
Standard CRC32 (poly 0xEDB88320, reflected). Incremental over uncompressed bytes.
Compression method 8 = RFC 1951 Deflate (reuse existing inflate impl; encoder = LZ77 + Huffman).

### Fast Parallel Unzip
Seek central directory (end-of-central-dir at file tail). Parse all entries to get
(local_header_offset, compressed_size). Dispatch goroutine/fiber per entry; each reads
its slice independently. Parallel decompression of independent entries — no ordering constraint.

---

## 2. WebP Image Format

### Container (RIFF-based)
```
Bytes 0-3:   "RIFF"
Bytes 4-7:   File size - 8 (uint32 LE)
Bytes 8-11:  "WEBP"
Then chunks: [FourCC 4B][Size 4B LE][Payload, padded to even]
```

### Chunk Types
| FourCC | Purpose |
|--------|---------|
| `VP8 ` | Lossy bitstream (VP8 key frame) |
| `VP8L` | Lossless bitstream |
| `VP8X` | Extended features flag chunk (12 bytes) |
| `ALPH` | Alpha channel (separate from VP8) |
| `ANIM`/`ANMF` | Animation global/frame |
| `ICCP`/`EXIF`/`XMP ` | Metadata |

### Simple Lossy WebP (decoder-only, minimal impl)
File = RIFF/WEBP header + single `VP8 ` chunk. VP8 data starts with 3-byte frame tag:
- Bits 0: key frame (must be 0 for intra)
- Bits 1-3: version (0,1,2,3)
- Bit 4: show_frame
- Bits 5-18: first_part_size

Then 3-byte start code: 0x9D 0x01 0x2A, followed by width/height (14-bit each).

VP8 codec: boolean arithmetic coder, 16x16 macroblocks, intra prediction (DC/V/H/TrueMotion),
4x4 DCT coefficients, quantization, zigzag, entropy coded with 4 probability trees.

### Minimal Encoder Strategy
For a browser cache/thumbnail encoder, VP8L (lossless) is simpler to implement:
- Color transform + subtract-green transform
- LZ77 backward references on pixel values
- Huffman coded output
Saves ~26% vs PNG lossless. For lossy, delegate to a 1-pass DCT quantizer:
1. YUV conversion, 2. 8x8 DCT per block, 3. quantize with fixed table, 4. Huffman encode.
WebP lossy = 25-35% smaller than JPEG at equivalent SSIM.

---

## 3. HTTP/2 Multiplexing

### Frame Header (9 bytes, all frames)
```
Length         24 bits  (payload bytes, max 16MB if SETTINGS_MAX_FRAME_SIZE set)
Type           8 bits   (0=DATA,1=HEADERS,2=PRIORITY,3=RST_STREAM,4=SETTINGS,
                         6=PUSH_PROMISE,7=PING,8=GOAWAY,9=WINDOW_UPDATE,10=CONTINUATION)
Flags          8 bits
Reserved       1 bit
Stream ID      31 bits  (0 = connection-level)
```

### Stream Concurrency
- `SETTINGS_MAX_CONCURRENT_STREAMS` (type=0x03): server advertises limit.
  Default: unlimited but typically 100-200 in practice.
- Client-initiated streams: odd IDs (1,3,5,...). Server-push: even IDs.
- New stream = send HEADERS frame with next odd stream ID.

### Flow Control
- Initial window: 65535 bytes per stream and connection (set via SETTINGS_INITIAL_WINDOW_SIZE).
- Sender decrements window per DATA frame sent. Receiver sends WINDOW_UPDATE to replenish.
- WINDOW_UPDATE payload: 4 bytes, 31-bit increment (must be > 0).
- Strategy: receiver sends WINDOW_UPDATE when consumed > window/2.

### Prioritization (RFC 9113 note)
PRIORITY frame (type=0x02) is **deprecated** in RFC 9113. Use RFC 9218 extensible priorities
(via `Priority` header or PRIORITY_UPDATE frame) instead. For implementation: skip PRIORITY
frames (ignore, don't error), implement RFC 9218 urgency levels (0-7) for scheduling.

### Optimal Parallel Resource Loading
1. Open single TCP+TLS connection. Send connection preface (24-byte magic + SETTINGS).
2. Issue all requests as concurrent HEADERS frames on streams 1,3,5,...
3. Track per-stream window; send WINDOW_UPDATE eagerly on each DATA received.
4. Schedule dispatch by RFC 9218 urgency: CSS(0) > JS(1) > fonts(2) > images(4).

### HPACK (header compression)
Static table: 61 pre-defined header entries. Dynamic table: LRU, default 4096 bytes.
Literal headers: name/value literals with optional indexing.

---

## 4. QUIC + HTTP/3

### QUIC Packet Types (RFC 9000)
| Type | Purpose | Packet Number Space |
|------|---------|-------------------|
| Initial | ClientHello/ServerHello, address validation | Initial |
| 0-RTT | Early data (client) | 0-RTT |
| Handshake | TLS Finished, certs | Handshake |
| Retry | Server address validation token | N/A |
| 1-RTT (Short header) | Application data | Application |

### Long Header format (Initial/Handshake/0-RTT)
```
Byte 0: Header form(1)=1, Fixed(1)=1, PacketType(2), TypeSpecific(4)
Bytes 1-4: Version (4 bytes)
Byte 5: DCIL (4 bits) + SCIL (4 bits)
...DCID, SCID, token length, token, length (varint), packet number, payload
```
Short header (1-RTT): Byte0 bit7=0, then DCID only, then packet number.

### TLS 1.3 Integration
- NO separate TLS record layer. TLS messages are QUIC CRYPTO frames.
- Three packet number spaces (Initial/Handshake/1-RTT) with separate keys.
- Initial keys derived from DCID using HKDF-SHA256 with fixed salt.
- 0-RTT keys from PSK; 1-RTT keys from TLS master secret.
- QUIC replaces TLS record layer encryption with AEAD (AES-128-GCM or ChaCha20-Poly1305).

### Loss Detection & Congestion (RFC 9002 - NewReno baseline)
- ACK frames: up to 256 ACK ranges, ack_delay field.
- Loss threshold: packet N lost if packet_number >= N + kPacketThreshold (=3) is ACKed.
- PTO (Probe Timeout): 2 * smoothed_RTT + max(4*RTT_var, kGranularity=1ms) + max_ack_delay.
- Congestion window: initial = min(10*max_datagram_size, max(14720, 2*max_datagram_size)).
- NewReno: slow start until ssthresh, then AIMD (cwnd += max_datagram_size * acked / cwnd).

### HTTP/3 on QUIC (RFC 9114)
- Each request = one bidirectional QUIC stream (stream 0,4,8,... client; 1,5,9,... server).
- Control streams: unidirectional, stream type 0x00 (H3) / 0x02 (QPACK encoder) / 0x03 (QPACK decoder).
- Frame format: `[Type: varint][Length: varint][Payload]`.
- HEADERS frame (type=0x01): QPACK-encoded field section.
- DATA frame (type=0x00): raw body bytes.
- QPACK: static table (99 entries), dynamic table (separate encoder/decoder streams for table updates).
- No head-of-line blocking: each stream independent at QUIC level.

### UDP Socket Requirements
- Non-blocking UDP socket, sendmsg/recvmsg with MSG_DONTWAIT.
- GSO (Generic Segmentation Offload) for batch sends on Linux.
- GRO for batch receives. Set SO_RXQ_OVFL to detect drops.
- IPv4: setsockopt IP_PKTINFO; IPv6: IPV6_RECVPKTINFO (for connection migration).

---

## 5. Bundle Dependency Tracking (Mold/Vite Style)

### Symbol Resolution (Linker Model)
Mold-style graph: nodes = object files/modules; edges = (undefined_symbol → defining_module).
Algorithm:
1. Pass 1: collect all exported symbols per module → symbol table (hash map).
2. Pass 2: for each undefined ref, look up symbol table → add dependency edge.
3. Topo-sort → link order. Cycles → collect into SCC (Tarjan's algorithm).

### JS ESM Module Graph (analogous)
```
nodes = {url → {imports: [url], exports: [name], size: bytes}}
edges = import statements (static) + dynamic import() calls

Walk:
  queue = [entry_points]
  visited = {}
  while queue not empty:
    m = dequeue
    if m in visited: skip
    visited.add(m)
    parse m → collect static imports
    for dep in imports: enqueue dep
```

### Chunk Splitting Strategy (Vite-style)
1. **Vendor chunk**: modules in `node_modules/` that are shared by ≥ 2 entry points.
2. **Dynamic boundary**: `import()` call → new async chunk boundary.
3. **Threshold splitting**: if shared module size > minChunkSize (default 10KB) and
   referenced by ≥ minSharedCount (default 2) entry chunks → split to shared chunk.
4. **Common library detection**:
   - Count reference_count[module] across all entry chunks.
   - If count ≥ threshold AND size > min_size: extract to shared chunk.

### Import Map / ESM Graph Walking for Browser
```
fn build_graph(entry: URL) -> Graph:
  graph = Graph{}
  worklist = [entry]
  while worklist not empty:
    url = worklist.pop()
    if graph.has(url): continue
    src = fetch(url)
    imports = parse_static_imports(src)   // regex: /^import .* from ['"](.+)['"]/m
    dyn_imports = parse_dynamic_imports(src) // /import\(['"](.+)['"]\)/
    graph.add_node(url, imports + dyn_imports)
    worklist.extend(imports)
  return graph

fn split_chunks(graph, threshold=2, min_size=10240):
  ref_count = count_refs(graph)
  shared = {m for m in graph.nodes if ref_count[m] >= threshold and size(m) > min_size}
  return partition(graph, shared)
```

---

## 6. Bloom Filter Cache

### Standard Bloom Filter
- **Structure**: bit array of m bits + k independent hash functions.
- **Add**: set bits at positions h_1(x)..h_k(x).
- **Query**: return true iff ALL k positions are set (false positives possible, no false negatives).

### Optimal Parameters
Given n expected items, target FPR ε:
```
m = ceil(-n * ln(ε) / (ln(2)²)  bits
k = round((m/n) * ln(2))        hash functions
```
Practical values for browser URL cache:
| n URLs | FPR   | m (bits) | Bytes  | k hashes |
|--------|-------|----------|--------|----------|
| 10,000 | 1%    | 95,851   | 11 KB  | 6        |
| 10,000 | 0.1%  | 143,776  | 17 KB  | 9        |
| 100,000| 1%    | 958,506  | 117 KB | 6        |

**vs LRU**: 10k entries with URL+ETag+Last-Modified ≈ 1.25 MB. Bloom = 11 KB → **106x smaller**.
(Bloom is a pre-filter; still need a small cache for the actual ETag/Last-Modified values.)

### Hash Functions
Use double hashing: `h_i(x) = (h1(x) + i * h2(x)) mod m`.
h1 = FNV-1a 64-bit, h2 = xxHash64. Avoids k independent hash impls.

### Counting Bloom Filter (for deletion/TTL)
Replace each bit with a 4-bit counter. Size: 4x standard. Supports delete (decrement counters).
Overflow (counter > 15): saturate at 15.

### TTL / Aging Strategy
**Time-bucketed approach** (recommended for cache validation):
```
struct TimedBloom:
  buckets: [Bloom; NUM_BUCKETS]  // e.g., 8 buckets, 1 hour each
  current: u8                    // index of active bucket
  created_at: [u64; NUM_BUCKETS] // epoch seconds per bucket

fn add(url):
  rotate_if_needed()  // if now - created_at[current] > bucket_ttl: advance current, clear next
  buckets[current].add(url)

fn query(url) -> bool:
  any(b.query(url) for b in buckets)  // union across all live buckets
```
This gives sliding-window TTL without exact per-entry timestamps. 8 buckets × 17KB = 136 KB
for 10k URLs per hour × 8 hours coverage at 0.1% FPR.

### Cache Validation Usage Pattern
```
fn should_revalidate(url, etag, last_modified) -> bool:
  key = hash(url + etag + last_modified)
  if bloom.query(key): return false  // probably fresh, skip request
  // else: bloom miss → definitely need to revalidate
  // After successful 304: bloom.add(key)
```

---

## Implementation Priorities

Ordered by impact-to-effort ratio for a browser in Simple:

1. **HTTP/2 multiplexing** — highest network impact, protocol is mature and well-specified.
   Start with frame parser + stream state machine + HPACK static table only.

2. **Bloom filter cache** — tiny impl (< 200 lines), immediate 106x memory savings for
   cache-validation pre-filter. Use double-hashing + time buckets.

3. **ZIP extraction** — needed for .wasm/.zip resource bundles. Streaming approach first
   (no central dir needed), parallel decompression second. Reuse existing inflate.

4. **Bundle dependency graph** — ESM import graph walk + threshold chunk splitter.
   Pure algorithm, no protocol work. Critical for reducing initial JS payload.

5. **QUIC + HTTP/3** — large impl (TLS 1.3 integration, packet crypto, loss detection).
   Implement as separate transport layer; use existing TLS 1.3 if available.

6. **WebP decoder** — implement VP8L (lossless) first (simpler arithmetic), then VP8 lossy.
   Encoder: defer unless image optimization pipeline is in scope.
