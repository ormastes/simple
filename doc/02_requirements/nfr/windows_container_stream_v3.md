# Windows stream nonfunctional requirements

The approved profile uses one observed processor group and no inherited host
Job. CPU grants must map exactly to the native hard-cap quantum; memory and CPU
settings require actual readback. Helper lifetime is independently bounded and
is not truncated by launch-grant expiry.

Native input has one 4096-byte pending prefix; output reads are at most8192
bytes. Producer hashing is bounded to256 MiB and checks admission expiry between
reads. Engine protocol bounds are16 KiB headers,256 KiB control bodies and1 MiB
frames/pending data. Native synchronous filesystem calls retain their OS latency
limitations; no hard real-time cancellation guarantee is claimed.

Every native failure must retain cleanup ownership until exact completion is
observed. Single-reader discipline and separate ongoing input/resize authority
are mandatory. All Windows latency, memory and enforcement measurements remain
NOT_RUN until a qualified host fixture supplies them.
