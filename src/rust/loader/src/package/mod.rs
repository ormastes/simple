//! Simple Package Format (SPK) for distributable packages.
//!
//! # Package Structure
//!
//! ```text
//! ┌────────────────────────────┐ ← 0x0000
//! │   Executable Stub (ELF/PE) │  Uncompressed, platform-specific
//! │   (finds and loads SSMF)   │
//! ├────────────────────────────┤ ← stub_size
//! │   Settlement (SSMF)        │  Uncompressed code/data sections
//! │   - Code section (RX)      │
//! │   - Data section (RW)      │
//! │   - Indirection tables     │
//! ├────────────────────────────┤ ← ssmf_end
//! │   Resources (ZIP)          │  Compressed assets/stdlib
//! │   - lib/ (stdlib modules)  │
//! │   - assets/ (resources)    │
//! ├────────────────────────────┤ ← resources_end
//! │   Manifest Section         │  Uncompressed TOML
//! │   - simple.toml            │
//! │   - simple.lock            │
//! ├────────────────────────────┤ ← manifest_end
//! │   Package Trailer (SPK)    │  Fixed size, always at end
//! │   - Magic: "SPK1"          │
//! │   - Section offsets        │
//! │   - Checksums              │
//! └────────────────────────────┘ ← EOF
//! ```
//!
//! # Design Rationale
//!
//! - **Executable first**: OS can directly execute the file
//! - **Settlement uncompressed**: Code must be directly mappable
//! - **Resources compressed**: Save space for assets/stdlib
//! - **Manifest uncompressed**: Human-readable, tools can inspect
//! - **Trailer at end**: Easy to find from EOF, append-friendly

mod format;
mod reader;
mod writer;

pub use format::*;
pub use reader::*;
pub use writer::*;
