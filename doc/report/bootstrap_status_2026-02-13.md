# Bootstrap Chain Status - 2026-02-13

## Your Question
> "seed build, seed to core build, core to core self build, core to full build. full to full self build done? is all script do it?"

## Answer

**Bootstrap Chain Status:**
1. ✅ **Seed build** - DONE (seed_cpp compiled, 105KB)
2. ✅ **Seed → core build** - DONE (core1 binary created, 183KB)
3. ❌ **Core → core self build** - **BLOCKED** (core1 is a stub)
4. ❌ **Core → full build** - **BLOCKED** (depends on #3)
5. ❌ **Full → full self build** - **BLOCKED** (depends on #3-4)

**Script Status:** `script/bootstrap-fixed.sh` automates steps 1-2 only, NOT the full chain.

---

## Critical Limitation Discovered

**seed_cpp generates stub binaries, not working executables.**

### Evidence

**Source code has full compiler logic:**
```simple
# src/compiler_core/main.spl:366
fn main() -> i32:
    val args = sys_get_args()
    # ... full CLI parsing and compilation logic ...
```

**But generated C++ is just a stub:**
```cpp
// build/bootstrap/core1.cpp:14432
int main(int argc, char** argv) {
    spl_init_args(argc, argv);
    __module_init();
    return 0;
}
```

**Verification:**
```bash
$ ./build/bootstrap/core1
(no output - program does nothing)
```

### Root Cause

**seed_cpp architecture limitation:** It transpiles Simple module code to C++ library code, but does NOT transpile `fn main()` into the C++ `int main()` entry point. It always generates a stub main() that only initializes global variables.

This means seed_cpp can create **libraries** but not **executables**.

---

## What Works

✅ seed_cpp can transpile 383 Simple files (44K LOC)
✅ Generates valid C++ code (14,437 lines)
✅ Compiles to working binary (passes all linker checks)
✅ All compiler functions exist as library code

## What Doesn't Work

❌ The binary cannot compile Simple code
❌ No CLI interface (main() is stub)
❌ Cannot proceed with self-hosting
❌ Steps 3-5 of bootstrap blocked

---

## Options Forward

### Option A: Fix seed_cpp to transpile main()
**Effort:** 1-2 days C++ work
**Complexity:** High - requires understanding seed_cpp's architecture
**Risk:** Medium - could break existing transpilation

### Option B: Use pre-built compiler for bootstrap
**Effort:** Immediate
**Approach:** Use `bin/release/simple` (33MB pre-built) to compile compiler_core
**Status:** This already works - it's how the project normally builds

### Option C: Document seed_cpp as library-only transpiler
**Effort:** Low
**Approach:** Accept seed_cpp limitation, use it only for library code
**Note:** The 33MB runtime already provides full bootstrap capability

---

## Recommendation

**Option B** - The project already has a working bootstrap path via `bin/release/simple`. The seed_cpp path was an experiment to build from minimal C++ sources, but it's blocked by this architectural limitation.

The practical bootstrap chain that works today:
```bash
bin/release/simple build              # Uses pre-built runtime
bin/simple test                        # 604/604 tests pass
```

If true "from-scratch" bootstrap is critical, pursue **Option A** to fix seed_cpp's main() handling. Otherwise, the existing path is production-ready.
