# Capturing Terminal Control Sequences - Research Summary

## Problem

Testing terminal applications like REPLs requires capturing not just text output, but also:
- ANSI escape sequences (colors, cursor movement)
- Control characters (backspace, tab, etc.)
- Terminal size changes
- OSC sequences

Standard pipes don't work because programs detect they're not connected to a TTY and disable these features.

## Solution: PTY (Pseudo-Terminal)

A PTY creates a virtual terminal with two endpoints:
- **Controller** (your test program)
- **Controlled** (the spawned process)

The spawned process thinks it's in a real terminal and emits all control sequences.

## Rust Crates Comparison

| Crate | Use Case | Platform | Complexity | Capture Quality |
|-------|----------|----------|------------|-----------------|
| [portable-pty](https://crates.io/crates/portable-pty) | Full PTY control | Unix + Windows | Medium | **Excellent** ✅ |
| [rexpect](https://crates.io/crates/rexpect) | pexpect-style testing | Unix only | Low | Good |
| [expectrl](https://docs.rs/expectrl) | Modern expect | Unix + Windows | Low | Good |
| [term-transcript](https://lib.rs/crates/term-transcript) | Snapshot testing | Unix + Windows | Low | Limited (SGR only) |

## Recommended: portable-pty

**Best for:** Capturing all terminal sequences including cursor movement, colors, and control codes.

**Source:** [DeveloperLife - Capturing Build Progress with PTY](https://developerlife.com/2025/08/10/pty-rust-osc-seq/) (August 2025)

### Installation

```toml
[dependencies]
portable-pty = "0.8"
```

### Example: Testing REPL Backspace

```rust
use portable_pty::{native_pty_system, CommandBuilder, PtySize};
use std::io::{Read, Write};

fn test_repl_backspace() -> Result<(), Box<dyn std::error::Error>> {
    // Create PTY
    let pty_system = native_pty_system();
    let pair = pty_system.openpty(PtySize {
        rows: 24,
        cols: 80,
        pixel_width: 0,
        pixel_height: 0,
    })?;

    // Spawn REPL
    let mut cmd = CommandBuilder::new("./target/debug/simple");
    let mut child = pair.slave.spawn_command(cmd)?;

    // IMPORTANT: Drop slave in parent to prevent deadlock
    drop(pair.slave);

    // Get I/O handles
    let mut reader = pair.master.try_clone_reader()?;
    let mut writer = pair.master.take_writer()?;

    // Wait for startup
    std::thread::sleep(std::time::Duration::from_millis(500));

    // Consume startup output
    let mut buf = [0u8; 4096];
    reader.read(&mut buf)?;

    // Test: Tab + Backspace
    writer.write_all(b"\t")?;      // Tab (insert 4 spaces)
    std::thread::sleep(std::time::Duration::from_millis(100));

    writer.write_all(b"\x7f")?;    // Backspace
    std::thread::sleep(std::time::Duration::from_millis(100));

    // Read output (contains control sequences)
    let n = reader.read(&mut buf)?;
    let output = String::from_utf8_lossy(&buf[..n]);

    // Check for cursor movement sequences
    if output.contains("\x1b[") {  // ANSI CSI sequence
        println!("✓ Captured terminal control sequences");
        println!("  Output: {:?}", output);

        // Parse cursor movements to verify backspace worked
        // Example: "\x1b[4C" = move cursor right 4 positions
        //          "\x1b[4D" = move cursor left 4 positions
    }

    // Cleanup
    writer.write_all(b"\x04")?;  // Ctrl+D to exit
    child.wait()?;

    Ok(())
}
```

### Key Points

1. **Drop the slave endpoint** after spawning to avoid deadlock
2. **Sleep between operations** to allow terminal to process
3. **Look for ANSI sequences**:
   - `\x1b[nC` = cursor right n positions
   - `\x1b[nD` = cursor left n positions
   - `\x1b[K` = clear to end of line
4. **Set TERM environment** for better compatibility:
   ```rust
   cmd.env("TERM", "xterm-256color");
   ```

## Alternative: rexpect (Simpler)

**Best for:** Quick scripted tests without parsing raw sequences.

**Source:** [Rust Adventure - Testing Interactive CLIs](https://www.rustadventure.dev/building-a-digital-garden-cli/clap-v4/testing-interactive-clis-with-rexpect) (2024)

### Installation

```toml
[dependencies]
rexpect = "0.5"
```

### Example

```rust
use rexpect::spawn;

fn test_backspace() -> Result<(), rexpect::error::Error> {
    let mut p = spawn("./target/debug/simple", Some(5000))?;

    // Wait for prompt
    p.exp_string(">>>")?;

    // Send Tab
    p.send("\t")?;

    // Send Backspace
    p.send("\x7f")?;

    // Verify still at prompt (spaces were deleted)
    p.exp_string(">>>")?;

    Ok(())
}
```

**Limitations:**
- Unix only (doesn't compile on Windows)
- Less control over raw output
- Can't easily inspect control sequences

## For Our REPL Test

**Recommendation:** Use `portable-pty` for definitive testing:

1. Capture raw terminal output with all sequences
2. Parse ANSI CSI codes to detect cursor movement
3. Verify that backspace causes cursor to move left 4 positions (full indent)
4. Check that cursor position matches expected state

**Why portable-pty over rexpect:**
- Cross-platform (Windows support for future)
- Full sequence capture (can verify exact terminal behavior)
- Active maintenance (used in major projects like [WezTerm](https://wezfurlong.org/wezterm/))

## Terminal Control Sequence Reference

Common sequences to look for in output:

| Sequence | Meaning | Expected on... |
|----------|---------|----------------|
| `\x1b[4C` | Cursor right 4 | Tab insertion |
| `\x1b[4D` | Cursor left 4 | Backspace on 4 spaces |
| `\x1b[K` | Clear line from cursor | Line clearing |
| `\x1b[1D` | Cursor left 1 | Normal backspace |
| `\t` | Tab character | Tab key (becomes spaces in REPL) |
| `\x7f` | DEL/Backspace | Backspace key |

## Sources

- [DeveloperLife: PTY and OSC Sequences](https://developerlife.com/2025/08/10/pty-rust-osc-seq/)
- [Rust Adventure: Testing Interactive CLIs with rexpect](https://www.rustadventure.dev/building-a-digital-garden-cli/clap-v4/testing-interactive-clis-with-rexpect)
- [portable-pty on crates.io](https://crates.io/crates/portable-pty)
- [rexpect on crates.io](https://crates.io/crates/rexpect)
- [expectrl documentation](https://docs.rs/expectrl)
- [term-transcript on lib.rs](https://lib.rs/crates/term-transcript)
- [pexpect documentation](https://pexpect.readthedocs.io/en/stable/)
