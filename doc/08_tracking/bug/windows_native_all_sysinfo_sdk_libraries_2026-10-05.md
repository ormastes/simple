# Pure-Simple aggregate runtime links omit Windows sysinfo libraries

The rebuilt Phase2 compiler's 1177 modules compiled successfully but its old
seed link failed on 16 imports from the aggregate runtime's sysinfo objects.
The retained-object relink succeeded after supplying the SDK libraries.
Separately inspecting the pure-Simple native-all support owner showed the
same omission in both MSVC and MinGW lists. Fix those lists so future
self-hosted aggregate links include Pdh, NetApi32, Psapi and PowrProf.

This patch does not rebuild the old seed or change a frozen compiler. Rust
link_config already contains these dependencies in current source. The
existing archive predicate continues to exclude core-only links. Three
native scenarios cover MSVC slash variants, MinGW argument spelling and
the core-only exclusion. They are UNRUN pending native test qualification.

Evidence: p2-next407be-cranelift80/owner/build.log SHA-256
`4f981048283f72b79a1571c652ed1d7e32da0236ce823de23cd3849e726ec704`;
retained objects `C:/dev/native-objects-YHP9OJ`; successful relink candidate
SHA-256 `27ac2358f22f28c9a43ec3ab47ac3957d5e2b293fc8b44fc52e573512f0c4c69`.
The repaired pure-Simple argument generator still requires native verification;
the historical link-only success is supporting dependency evidence.
