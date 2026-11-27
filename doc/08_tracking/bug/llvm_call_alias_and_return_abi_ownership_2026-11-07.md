# LLVM call alias and return ABI ownership

Status: source repairs and direct MIR regressions authored; runtime verification pending.

The LLVM source review found four related call-emission defects after the
local `env_get` repair landed in PR #7440:

1. Bare `get_args`, `get_cli_args`, `sys_get_args`, and `eprint` calls always
   route to runtime aliases, including source-local definitions. A local
   `fn get_args() -> i64: 42` is instead called as `rt_get_args`. The bootstrap
   return override independently treats local argv helpers as pointer results.
2. Function-reference operands overwrite pre-discovered local return types
   using the call operand's type. A local definition returning `f64` plus an
   erased `FuncPtr(... -> i64)` call operand emits a `call i64` beside a
   `define double`. Parameter metadata already protects declaration authority;
   both indexed and legacy return-metadata paths lacked that protection.
3. A direct `Call(nil, ...)` always emits `call void`, even when the definition
   or extern signature declares a floating or scalar return. Discarding a
   result must retain its calling convention.
4. Fixed extern `u8` return metadata loses unsigned identity, and generic
   `Call` through a function-pointer local overwrites its already typed unsigned
   destination with a missing named-callee lookup. Widening can consequently
   sign-extend instead of zero-extending.

The patch extends pre-emission local alias ownership to the four additional
names; it preserves the existing `env_get` guards. A call-site return view now
seeds type and signedness only when no declaration return is known. Discarded
calls use their declared return type. Calls without a named return entry keep
the typed MIR destination's signedness.

`test/01_unit/compiler/backend/llvm_call_abi_owner_spec.spl` contains the authored
reproductions and prevention controls. It covers local aliases in both emission
orders with explicit bootstrap off/on; bodyless alias routing; double return
authority; discarded direct results; extern and local-pointer unsigned returns;
both function-reference operand entry points; and dedicated `CallIndirect`
consumed/discarded floating-result preservation. No `CallIndirect` implementation
change is claimed: its existing explicit signature path remains distinct from
generic `Call` through a local function pointer.

Evidence limits and separate owners:

- No admitted rebuilt pure-Simple runtime is available. These tests have not
  executed. Source review and authored MIR cases are not runtime PASS evidence.
- Local `get_args()[i]`/`get_cli_args()[i]` expressions can be rewritten upstream
  by the owner-blind bootstrap CLI-index shortcut. Local `eprint` calls can also
  be intercepted upstream by name. Those MIR findings were sent to the MIR
  lane; LLVM direct-MIR coverage does not claim those source paths are fixed.
- The preserved nonlocal `eprint` route targets `rt_eprint`, for which source
  review found no owned runtime provider. Its control test establishes routing
  preservation only, not successful linking or a qualified runtime ABI.
- The erased-return and discarded-result reproductions directly exercise the
  supported MIR backend contract; source reachability through every frontend
  mode remains unverified.

Resume by rebuilding/admitting a producer containing the exact combined LLVM
and memory changes, then execute this spec, the existing `env_get` ownership and
inline-text-extern ABI regressions, and compiler/core/lib plus MCP smoke gates.
