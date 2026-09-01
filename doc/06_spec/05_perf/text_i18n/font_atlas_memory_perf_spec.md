# Shared font-atlas memory-performance specification

This executable specification measures CPU/reference atlas-subrectangle
extraction and proves that Engine2D and Engine3D cache identities remain
distinct while sharing the composite semantic owner.

The receipt records atlas CPU bytes, extracted output bytes, iterations,
runtime-owned retained/auxiliary/capacity growth, and counter availability.
Device memory, upload bytes, queue completion, fences, and readback are always
reported unavailable here because CPU reference execution cannot prove them.

Native Engine2D and Engine3D device runs remain mandatory release evidence.
