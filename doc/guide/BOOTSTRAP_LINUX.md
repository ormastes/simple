# Linux Bootstrap Package

## Summary

✅ Successfully created Linux x86_64 bootstrap package

## Package Details

- **File**: `bin/release/simple-bootstrap-0.5.1-alpha-linux-x86_64.spk`
- **Size**: 62 MB (includes runtime + full stdlib + all apps)
- **Platform**: linux-x86_64
- **Version**: 0.5.1-alpha
- **Runtime**: Pre-built binary from bin/release/simple (v0.4.0-alpha.1)

## Package Contents

```
bin/
  simple                    # 27MB runtime binary
lib/simple/
  stdlib/                   # Full standard library source
  app/                      # All application modules
manifest.sdn               # Package metadata
```

## Installation

```bash
# Extract package
tar -xzf bin/release/simple-bootstrap-0.5.1-alpha-linux-x86_64.spk -C ~/.local

# Add to PATH
export PATH="$HOME/.local/bin:$PATH"

# Verify
simple --version
```

## Testing

Package verified working:
- ✅ Extraction successful
- ✅ Binary executes
- ✅ Version check passes
- ✅ All source files included

## C Backend Bootstrap

For building from generated C++20 source (alternative to binary distribution):

```bash
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
cmake -B build -G Ninja -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build
mkdir -p bin/bootstrap/cpp && cp build/simple bin/bootstrap/cpp/simple
```

See `doc/guide/bootstrap.md` for the full bootstrap guide.

## Notes

- This is a **pure binary distribution** - no compilation needed
- The runtime is pre-compiled for performance
- All compiler/stdlib/tools are in Simple source code
- Compatible with Linux x86_64 systems (kernel 3.2.0+)

