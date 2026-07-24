# SimpleOS filesystem toolchain and servers design — TLDR

- VFS header/phdr/range reads feed the existing ELF mapper.
- Target stamp + ELF validation gate every role path.
- HTTP asserts two real responses.
- DB asserts create → insert → select of a known value.
- Clang and Simple each prove guest path, version, compile, output, and run.
- Any missing/stale/fake/preloaded/host-only evidence returns nonzero.
- Stage 4 first builds a fingerprinted `ModuleSurface` index, then reparses and
  lowers one full Module at a time while retaining HIR.
- Ordinary bodies/defaults/constant values are omitted; imported trait defaults
  and enum field-default expressions are the only executable AST exceptions.
- Streaming requires Stage4 AOT + entry-closure + low-memory +
  `SIMPLE_BOOTSTRAP_STAGE4=1`; VHDL and normal paths are unchanged.
- The first ten unique ordered post-release markers must average at most 25,000
  retained heap objects/file; termination is requested at marker ten.
