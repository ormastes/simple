#!/usr/bin/env bash
# Copy the SimpleOS target specs and libstd PAL into an upstream `rust` checkout.
#
# Usage: ./apply.sh <path-to-rust-src>
# Prerequisite: the target checkout is on the `simpleos` fork branch and clean.
set -euo pipefail

if [[ $# -lt 1 ]]; then
    echo "usage: $0 <path-to-rust-src>" >&2
    exit 2
fi

RUST_SRC="$1"
if [[ ! -d "$RUST_SRC/compiler/rustc_target/src/spec/targets" ]]; then
    echo "error: '$RUST_SRC' does not look like a rust source tree" >&2
    exit 1
fi

HERE="$(cd "$(dirname "$0")" && pwd)"

copy() {
    local src="$1" dst="$2"
    mkdir -p "$(dirname "$dst")"
    cp -v "$src" "$dst"
}

# --- Built-in target specs -------------------------------------------------
for arch in x86_64 aarch64 riscv64gc riscv32imac; do
    copy "$HERE/compiler/rustc_target/src/spec/targets/${arch}_unknown_simpleos.rs" \
         "$RUST_SRC/compiler/rustc_target/src/spec/targets/${arch}_unknown_simpleos.rs"
done

# --- libstd PAL ------------------------------------------------------------
PAL_DST="$RUST_SRC/library/std/src/sys/pal/simpleos"
mkdir -p "$PAL_DST"
for f in mod.rs alloc.rs args.rs env.rs exit.rs fs.rs io.rs stdio.rs time.rs \
         thread.rs process.rs pipe.rs net.rs; do
    copy "$HERE/library/std/src/sys/pal/simpleos/$f" "$PAL_DST/$f"
done

# --- libstd public os::simpleos module -------------------------------------
OS_DST="$RUST_SRC/library/std/src/os/simpleos"
mkdir -p "$OS_DST"
for f in mod.rs ffi.rs raw.rs; do
    copy "$HERE/library/std/src/os/simpleos/$f" "$OS_DST/$f"
done

cat <<'NOTE'

--- manual follow-up required -----------------------------------------------
1. Edit compiler/rustc_target/src/spec/mod.rs and add the four SimpleOS
   triples to the `supported_targets!` macro (see
   compiler/rustc_target/src/spec/mod.rs.patch.md in this patch set).

2. Edit library/std/src/sys/pal/mod.rs and add a cfg arm so the new PAL is
   selected when `target_os = "simpleos"` (see
   library/std/src/sys/pal/mod.rs.patch.md in this patch set):

       } else if #[cfg(target_os = "simpleos")] {
           mod simpleos;
           pub use self::simpleos::*;
       }

3. Edit library/std/src/os/mod.rs and add the public re-export so
   `std::os::simpleos` is reachable from user code (see
   library/std/src/os/mod.rs.patch.md in this patch set):

       #[cfg(target_os = "simpleos")]
       pub mod simpleos;

4. Rebuild stage0 and then:
       rustc --target x86_64-unknown-simpleos examples/hello.rs
-----------------------------------------------------------------------------
NOTE
