# 4KB Page Locality - Phase 4 Complete

**Date:** 2025-12-28
**Phase:** 4 of 5 - SMF/ELF Linker Integration
**Features:** #2030-#2039 (10 features)
**Cumulative Progress:** 39/50 features (78%)

## Summary

Phase 4 implements the SMF/ELF linker integration for layout optimization. The `LayoutOptimizer` module provides section ordering, symbol grouping, profile-guided layout, and hot/cold code splitting to minimize page faults during startup.

## Features Implemented (#2030-#2039)

### Section Ordering by Phase (#2030-#2032)
| Feature | Description | Status |
|---------|-------------|--------|
| #2030 | LayoutSymbol struct with phase/size/callees | Completed |
| #2031 | sort_by_phase() ordering algorithm | Completed |
| #2032 | Phase priority constants | Completed |

### Symbol Grouping for Locality (#2033-#2035)
| Feature | Description | Status |
|---------|-------------|--------|
| #2033 | Call graph tracking in LayoutSymbol | Completed |
| #2034 | group_for_locality() bin packing | Completed |
| #2035 | Group ID assignment for 4KB pages | Completed |

### Profile-Guided Layout (#2036-#2037)
| Feature | Description | Status |
|---------|-------------|--------|
| #2036 | apply_profile_guided_layout() | Completed |
| #2037 | RecordedFunction integration | Completed |

### Hot/Cold Code Splitting (#2038-#2039)
| Feature | Description | Status |
|---------|-------------|--------|
| #2038 | split_hot_cold() separation | Completed |
| #2039 | LayoutSegment generation | Completed |

## Implementation Details

### New Module: linker/layout.rs

Created `src/compiler/src/linker/layout.rs` (~650 lines) with:

```rust
/// Symbol layout entry for optimization
pub struct LayoutSymbol {
    pub name: String,
    pub phase: LayoutPhase,
    pub size: u64,
    pub call_count: u64,
    pub callees: Vec<String>,
    pub is_anchor: bool,
    pub pinned: bool,
    pub group_id: Option<u32>,
}

/// Layout optimizer for organizing symbols and sections
pub struct LayoutOptimizer {
    symbols: Vec<LayoutSymbol>,
    config: Option<LayoutConfig>,
    recorded: HashMap<String, RecordedFunction>,
    next_group_id: u32,
    stats: LayoutStats,
}

/// Layout segment for linker script generation
pub struct LayoutSegment {
    pub name: String,      // e.g., ".text.startup"
    pub phase: LayoutPhase,
    pub symbols: Vec<String>,
    pub size: u64,
}
```

### Key Algorithms

#### Phase Ordering
```rust
pub fn sort_by_phase(&mut self) {
    self.symbols.sort_by(|a, b| {
        // First by phase priority (startup=0, first_frame=1, steady=2, cold=3)
        let phase_cmp = a.sort_priority().cmp(&b.sort_priority());
        if phase_cmp != std::cmp::Ordering::Equal {
            return phase_cmp;
        }
        // Within phase: anchors first, then by call count (higher = earlier)
        if a.is_anchor != b.is_anchor {
            return if a.is_anchor { Less } else { Greater };
        }
        b.call_count.cmp(&a.call_count)
    });
}
```

#### 4KB Page Bin Packing
```rust
pub fn group_for_locality(&mut self) {
    const PAGE_SIZE: u64 = 4096;

    let mut current_group = 0u32;
    let mut current_size = 0u64;

    for sym in &mut self.symbols {
        // Start new group if current page is full
        if current_size + sym.size > PAGE_SIZE && current_size > 0 {
            current_group += 1;
            current_size = 0;
        }

        sym.group_id = Some(current_group);
        current_size += sym.size;

        // Try to add callees to same group for locality
        for callee in &sym.callees {
            if let Some(callee_sym) = self.find_symbol_mut(callee) {
                if current_size + callee_sym.size <= PAGE_SIZE {
                    callee_sym.group_id = Some(current_group);
                    current_size += callee_sym.size;
                }
            }
        }
    }
}
```

#### Hot/Cold Splitting
```rust
pub fn split_hot_cold(&mut self) -> (Vec<LayoutSymbol>, Vec<LayoutSymbol>) {
    let mut hot = Vec::new();
    let mut cold = Vec::new();

    for sym in &self.symbols {
        match sym.phase {
            LayoutPhase::Startup | LayoutPhase::FirstFrame | LayoutPhase::Steady => {
                hot.push(sym.clone());
            }
            LayoutPhase::Cold => {
                cold.push(sym.clone());
            }
        }
    }

    (hot, cold)
}
```

### Segment Generation

Generates ELF-compatible section names:
- `.text.startup` - Startup phase code
- `.text.first_frame` - First frame code
- `.text` - Steady state (hot) code
- `.text.cold` - Rarely executed code

```rust
impl LayoutSegment {
    pub fn from_optimizer(optimizer: &LayoutOptimizer) -> Vec<Self> {
        vec![
            LayoutSegment { name: ".text.startup".to_string(), phase: Startup, ... },
            LayoutSegment { name: ".text.first_frame".to_string(), phase: FirstFrame, ... },
            LayoutSegment { name: ".text".to_string(), phase: Steady, ... },
            LayoutSegment { name: ".text.cold".to_string(), phase: Cold, ... },
        ]
    }
}
```

## Files Modified

| File | Changes |
|------|---------|
| `src/compiler/src/linker/layout.rs` | NEW - Layout optimization (~650 lines) |
| `src/compiler/src/linker/mod.rs` | Added layout module and exports |

## Test Coverage

The layout module includes 6 unit tests:
1. `test_layout_symbol_priority` - Validates phase priority ordering
2. `test_sort_by_phase` - Tests phase-based symbol sorting
3. `test_group_for_locality` - Tests 4KB page grouping
4. `test_split_hot_cold` - Tests hot/cold separation
5. `test_layout_segments` - Tests segment generation
6. `test_with_config` - Tests config-based phase assignment

## Usage Example

```rust
use simple_compiler::linker::{LayoutOptimizer, LayoutSegment};

// Create optimizer with layout config
let mut optimizer = LayoutOptimizer::with_config(layout_config);

// Add symbols from SMF
optimizer.add_smf_symbols(&smf_symbols);

// Apply profile-guided layout
optimizer.apply_profile_guided_layout();

// Sort by phase and group for locality
optimizer.sort_by_phase();
optimizer.group_for_locality();

// Generate linker segments
let segments = LayoutSegment::from_optimizer(&optimizer);

// Get ordered symbol names for linker
let ordered = optimizer.get_ordered_symbols();
```

## Phase Progression

| Phase | Features | Status | Progress |
|-------|----------|--------|----------|
| Phase 1 | #2000-#2008 (9) | Complete | Language & Parser + Compiler IR |
| Phase 2 | #2010-#2019 (10) | Complete | SDN Schema + Config Loader |
| Phase 3 | #2020-#2029 (10) | Complete | Test Framework Recording |
| Phase 4 | #2030-#2039 (10) | Complete | SMF/ELF Linker Integration |
| Phase 5 | #2040-#2049 (10) | Planned | Runtime Hot Path Analysis |

## Next Steps (Phase 5)

Phase 5 will implement Runtime Hot Path Analysis:
- Runtime profiling hooks for production builds
- Dynamic phase adjustment based on actual execution
- Feedback loop for layout optimization
- Performance metrics collection

## Build Status

- Workspace build: Passed
- Warnings: 127 (pre-existing, unrelated to this phase)

## Related Reports

- Phase 1: [4KB_PAGE_LOCALITY_PHASE1_2025-12-28.md](4KB_PAGE_LOCALITY_PHASE1_2025-12-28.md)
- Phase 2: [4KB_PAGE_LOCALITY_PHASE2_2025-12-28.md](4KB_PAGE_LOCALITY_PHASE2_2025-12-28.md)
- Phase 3: [4KB_PAGE_LOCALITY_PHASE3_2025-12-28.md](4KB_PAGE_LOCALITY_PHASE3_2025-12-28.md)
