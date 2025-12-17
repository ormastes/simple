// Type definitions for MIR lowering (mir/lower module)

use super::{
    blocks::Terminator,
    instructions::{BlockId, VReg},
    function::MirFunction,
};
use std::collections::HashMap;
use thiserror::Error;

//==============================================================================
// Contract Mode (CTR-040 to CTR-043)
//==============================================================================

/// Contract checking mode (--contracts flag)
///
/// Controls when contract checks (preconditions, postconditions, invariants)
/// are emitted during compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ContractMode {
    /// No contract checks emitted (CTR-040)
    Off,
    /// Only check contracts at public API boundaries (CTR-041)
    Boundary,
    /// Check all contracts (default) (CTR-042)
    #[default]
    All,
    /// Test mode: Check all contracts with rich diagnostics (CTR-043)
    ///
    /// In test mode, contract violations include:
    /// - Full function name and signature
    /// - The exact expression that failed
    /// - Source location (file, line, column) if available
    /// - Stack trace information
    Test,
}

impl ContractMode {
    /// Parse contract mode from string (CLI flag value)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "off" | "none" => Some(ContractMode::Off),
            "boundary" | "public" => Some(ContractMode::Boundary),
            "all" | "on" => Some(ContractMode::All),
            "test" | "debug" => Some(ContractMode::Test),
            _ => None,
        }
    }

    /// Get string representation for CLI/config
    pub fn as_str(&self) -> &'static str {
        match self {
            ContractMode::Off => "off",
            ContractMode::Boundary => "boundary",
            ContractMode::All => "all",
            ContractMode::Test => "test",
        }
    }

    /// Returns true if this mode includes rich diagnostics (CTR-043)
    pub fn has_rich_diagnostics(&self) -> bool {
        matches!(self, ContractMode::Test)
    }

    /// Returns true if this mode checks all contracts
    pub fn checks_all(&self) -> bool {
        matches!(self, ContractMode::All | ContractMode::Test)
    }
}

//==============================================================================
// Explicit State Machine (for formal verification)
//==============================================================================
// The lowerer state is made explicit to simplify verification.
// Instead of using Option<MirFunction> with implicit state transitions,
// we use an enum that encodes valid state combinations.
//
// This maps to a Lean state machine:
//   inductive LowererState
//     | idle
//     | lowering (func : MirFunction) (block : BlockId) (loop_stack : List LoopContext)
//
// Invariants:
//   - In `Lowering` state, `current_block` always refers to a valid block in `func`
//   - `loop_stack` tracks nested loops for break/continue

/// Loop context for break/continue handling
#[derive(Debug, Clone)]
pub struct LoopContext {
    /// Block to jump to on `continue`
    pub continue_target: BlockId,
    /// Block to jump to on `break`
    pub break_target: BlockId,
}

/// Context for contract lowering
#[derive(Debug, Clone, Default)]
pub struct ContractContext {
    /// Captured old() values: maps index to VReg holding the captured value
    pub old_captures: HashMap<usize, VReg>,
    /// VReg holding the return value (set before postcondition checks)
    pub return_value: Option<VReg>,
    /// Function name for error messages
    pub func_name: String,
    /// Whether the function is public (for boundary mode checks)
    pub is_public: bool,
}

/// Explicit lowerer state - makes state transitions verifiable
#[derive(Debug)]
pub enum LowererState {
    /// Not currently lowering any function
    Idle,
    /// Actively lowering a function
    Lowering {
        func: MirFunction,
        current_block: BlockId,
        loop_stack: Vec<LoopContext>,
        /// Contract context for Design by Contract support
        contract_ctx: ContractContext,
    },
}

impl LowererState {
    /// Check if we're in idle state
    pub fn is_idle(&self) -> bool {
        matches!(self, LowererState::Idle)
    }

    /// Check if we're lowering
    pub fn is_lowering(&self) -> bool {
        matches!(self, LowererState::Lowering { .. })
    }

    /// Get current block ID (returns error if idle - safe for verification)
    ///
    /// This is the preferred accessor for Lean-style verification.
    /// All state access should be fallible to match the Lean model.
    pub fn try_current_block(&self) -> MirLowerResult<BlockId> {
        match self {
            LowererState::Lowering { current_block, .. } => Ok(*current_block),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get current block ID (panics if idle - use only when state is known)
    ///
    /// **DEPRECATED**: This method panics on invalid state access.
    /// Prefer `try_current_block()` for verification-friendly code.
    /// Lean models use total functions - panicking breaks this property.
    #[deprecated(
        since = "0.1.0",
        note = "Use try_current_block() for Lean-compatible totality"
    )]
    pub fn current_block(&self) -> BlockId {
        self.try_current_block()
            .expect("Invariant violation: accessing block in idle state")
    }

    /// Get mutable reference to function (returns error if idle)
    pub fn try_func_mut(&mut self) -> MirLowerResult<&mut MirFunction> {
        match self {
            LowererState::Lowering { func, .. } => Ok(func),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Returns an error if in Idle state
    fn idle_state_error() -> MirLowerError {
        MirLowerError::InvalidState {
            expected: "Lowering".to_string(),
            found: "Idle".to_string(),
        }
    }

    /// Get loop stack (returns error if idle)
    pub fn try_loop_stack(&self) -> MirLowerResult<&Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Get mutable loop stack (returns error if idle)
    pub fn try_loop_stack_mut(&mut self) -> MirLowerResult<&mut Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Set current block (returns error if idle)
    pub fn try_set_current_block(&mut self, block: BlockId) -> MirLowerResult<()> {
        match self {
            LowererState::Lowering { current_block, .. } => {
                *current_block = block;
                Ok(())
            }
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Get loop depth for verification
    pub fn loop_depth(&self) -> usize {
        match self {
            LowererState::Lowering { loop_stack, .. } => loop_stack.len(),
            LowererState::Idle => 0,
        }
    }
}

/// Block building state - makes terminator state explicit
#[derive(Debug, Clone, PartialEq)]
pub enum BlockState {
    /// Block is open, accepting instructions
    Open,
    /// Block has been sealed with a terminator
    Sealed(Terminator),
}

impl BlockState {
    pub fn is_open(&self) -> bool {
        matches!(self, BlockState::Open)
    }

    pub fn is_sealed(&self) -> bool {
        matches!(self, BlockState::Sealed(_))
    }
}

#[derive(Error, Debug)]
pub enum MirLowerError {
    #[error("Unsupported HIR construct: {0}")]
    Unsupported(String),
    #[error("Invalid state: expected {expected}, found {found}")]
    InvalidState { expected: String, found: String },
    #[error("Break outside loop")]
    BreakOutsideLoop,
    #[error("Continue outside loop")]
    ContinueOutsideLoop,
}

pub type MirLowerResult<T> = Result<T, MirLowerError>;
