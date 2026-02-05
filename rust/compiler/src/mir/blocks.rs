//! MIR basic blocks and block builder.
//!
//! This module defines block types and the BlockBuilder for constructing
//! properly terminated blocks.

use super::effects::{EffectSet, HasEffects};
use super::instructions::{BlockId, MirInst, VReg};

/// Block terminator
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Return from function
    Return(Option<VReg>),

    /// Unconditional jump
    Jump(BlockId),

    /// Conditional branch
    Branch {
        cond: VReg,
        then_block: BlockId,
        else_block: BlockId,
    },

    /// Unreachable (after infinite loop, etc.)
    Unreachable,
}

impl Terminator {
    /// Check if this is a "real" terminator (not Unreachable placeholder)
    pub fn is_sealed(&self) -> bool {
        !matches!(self, Terminator::Unreachable)
    }

    /// Check if this terminator transfers control to another block
    pub fn is_branching(&self) -> bool {
        matches!(self, Terminator::Jump(_) | Terminator::Branch { .. })
    }

    /// Registers used by this terminator.
    pub fn uses(&self) -> Vec<VReg> {
        match self {
            Terminator::Return(Some(v)) => vec![*v],
            Terminator::Return(None) => vec![],
            Terminator::Jump(_) => vec![],
            Terminator::Branch { cond, .. } => vec![*cond],
            Terminator::Unreachable => vec![],
        }
    }

    /// Get all successor block IDs
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Return(_) => vec![],
            Terminator::Jump(target) => vec![*target],
            Terminator::Branch {
                then_block, else_block, ..
            } => vec![*then_block, *else_block],
            Terminator::Unreachable => vec![],
        }
    }
}

//==============================================================================
// Block Builder (for formal verification)
//==============================================================================
// BlockBuilder provides a type-safe way to construct blocks where the
// terminator state is tracked explicitly. This maps to a Lean state machine:
//
//   inductive BlockBuildState
//     | open (instructions : List MirInst)
//     | sealed (instructions : List MirInst) (terminator : Terminator)
//
// Invariant: Once sealed, no more instructions can be added.

/// Block build state - tracks whether block is open or sealed
#[derive(Debug, Clone, PartialEq)]
pub enum BlockBuildState {
    /// Block is open, accepting instructions
    Open { id: BlockId, instructions: Vec<MirInst> },
    /// Block has been sealed with a terminator
    Sealed {
        id: BlockId,
        instructions: Vec<MirInst>,
        terminator: Terminator,
    },
}

impl BlockBuildState {
    /// Create a new open block
    pub fn new(id: BlockId) -> Self {
        BlockBuildState::Open {
            id,
            instructions: Vec::new(),
        }
    }

    /// Check if block is open (can accept more instructions)
    pub fn is_open(&self) -> bool {
        matches!(self, BlockBuildState::Open { .. })
    }

    /// Check if block is sealed (has terminator)
    pub fn is_sealed(&self) -> bool {
        matches!(self, BlockBuildState::Sealed { .. })
    }

    /// Get block ID
    pub fn id(&self) -> BlockId {
        match self {
            BlockBuildState::Open { id, .. } => *id,
            BlockBuildState::Sealed { id, .. } => *id,
        }
    }

    /// Get instructions (regardless of state)
    pub fn instructions(&self) -> &[MirInst] {
        match self {
            BlockBuildState::Open { instructions, .. } => instructions,
            BlockBuildState::Sealed { instructions, .. } => instructions,
        }
    }

    /// Get terminator if sealed
    pub fn terminator(&self) -> Option<&Terminator> {
        match self {
            BlockBuildState::Open { .. } => None,
            BlockBuildState::Sealed { terminator, .. } => Some(terminator),
        }
    }
}

/// Type-safe block builder that enforces build state transitions
#[derive(Debug)]
pub struct BlockBuilder {
    state: BlockBuildState,
}

/// Error type for block building operations
#[derive(Debug, Clone, PartialEq)]
pub enum BlockBuildError {
    /// Tried to add instruction to sealed block
    AlreadySealed,
    /// Tried to seal an already sealed block
    AlreadySealedWith(Terminator),
    /// Tried to finalize an open block
    NotSealed,
}

impl BlockBuilder {
    /// Create a new block builder for the given block ID
    pub fn new(id: BlockId) -> Self {
        Self {
            state: BlockBuildState::new(id),
        }
    }

    /// Get current build state
    pub fn state(&self) -> &BlockBuildState {
        &self.state
    }

    /// Check if block is open
    pub fn is_open(&self) -> bool {
        self.state.is_open()
    }

    /// Check if block is sealed
    pub fn is_sealed(&self) -> bool {
        self.state.is_sealed()
    }

    /// Get block ID
    pub fn id(&self) -> BlockId {
        self.state.id()
    }

    /// Add an instruction to the block (only if open)
    pub fn push(&mut self, inst: MirInst) -> Result<(), BlockBuildError> {
        match &mut self.state {
            BlockBuildState::Open { instructions, .. } => {
                instructions.push(inst);
                Ok(())
            }
            BlockBuildState::Sealed { .. } => Err(BlockBuildError::AlreadySealed),
        }
    }

    /// Seal the block with a terminator (only if open)
    pub fn seal(&mut self, terminator: Terminator) -> Result<(), BlockBuildError> {
        match std::mem::replace(
            &mut self.state,
            BlockBuildState::Open {
                id: BlockId(0),
                instructions: Vec::new(),
            },
        ) {
            BlockBuildState::Open { id, instructions } => {
                self.state = BlockBuildState::Sealed {
                    id,
                    instructions,
                    terminator,
                };
                Ok(())
            }
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator: old_term,
            } => {
                // Restore the sealed state
                self.state = BlockBuildState::Sealed {
                    id,
                    instructions,
                    terminator: old_term.clone(),
                };
                Err(BlockBuildError::AlreadySealedWith(old_term))
            }
        }
    }

    /// Seal with jump if not already sealed (for fallthrough)
    pub fn seal_with_jump_if_open(&mut self, target: BlockId) {
        if self.is_open() {
            let _ = self.seal(Terminator::Jump(target));
        }
    }

    /// Finalize and return the completed block (only if sealed)
    pub fn finalize(self) -> Result<MirBlock, BlockBuildError> {
        match self.state {
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator,
            } => Ok(MirBlock {
                id,
                instructions,
                terminator,
            }),
            BlockBuildState::Open { .. } => Err(BlockBuildError::NotSealed),
        }
    }

    /// Force finalize - use Unreachable if not sealed (for compatibility)
    pub fn finalize_or_unreachable(self) -> MirBlock {
        match self.state {
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator,
            } => MirBlock {
                id,
                instructions,
                terminator,
            },
            BlockBuildState::Open { id, instructions } => MirBlock {
                id,
                instructions,
                terminator: Terminator::Unreachable,
            },
        }
    }
}

/// Basic block in MIR
#[derive(Debug, Clone)]
pub struct MirBlock {
    pub id: BlockId,
    pub instructions: Vec<MirInst>,
    pub terminator: Terminator,
}

impl MirBlock {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }

    /// Create from a block builder (must be sealed)
    pub fn from_builder(builder: BlockBuilder) -> Result<Self, BlockBuildError> {
        builder.finalize()
    }

    /// Check if block is properly terminated (not Unreachable)
    pub fn is_sealed(&self) -> bool {
        self.terminator.is_sealed()
    }

    /// Collect all effects in this block.
    pub fn effects(&self) -> EffectSet {
        let mut set = EffectSet::new();
        for inst in &self.instructions {
            set.push(inst.effect());
        }
        set
    }

    /// Check if this block is async (no blocking operations).
    pub fn is_async(&self) -> bool {
        self.effects().is_pipeline_safe()
    }

    /// Check if this block is nogc (no GC allocations).
    pub fn is_nogc(&self) -> bool {
        self.effects().is_nogc()
    }
}
