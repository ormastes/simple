//! RenderIR - Dynamic rendering instructions
//!
//! Low-level instructions for rendering templates with control flow.

use crate::parser::Expr;
use crate::ir::NodeId;

/// Virtual register for intermediate values
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Reg(pub u32);

/// Block identifier in the render CFG
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct BlockId(pub u32);

/// Render IR - control flow graph for dynamic rendering
#[derive(Debug, Clone, Default)]
pub struct RenderIR {
    /// All basic blocks
    pub blocks: Vec<RenderBlock>,
    /// Entry block
    pub entry: BlockId,
    /// Next register ID
    next_reg: u32,
    /// Next block ID
    next_block: u32,
}

impl RenderIR {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_reg(&mut self) -> Reg {
        let reg = Reg(self.next_reg);
        self.next_reg += 1;
        reg
    }

    pub fn alloc_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        id
    }

    pub fn add_block(&mut self, block: RenderBlock) -> BlockId {
        let id = self.alloc_block();
        self.blocks.push(block);
        id
    }
}

/// A basic block in the render CFG
#[derive(Debug, Clone)]
pub struct RenderBlock {
    pub id: BlockId,
    pub instructions: Vec<RenderInstr>,
    pub terminator: Terminator,
}

/// Render instruction
#[derive(Debug, Clone)]
pub enum RenderInstr {
    // State operations
    /// Load state field into register
    LoadState { dest: Reg, field: String },
    /// Store register value to state field
    StoreState { field: String, value: Reg },

    // Tree operations
    /// Create an element node
    CreateElement { dest: Reg, tag: String },
    /// Create a text node
    CreateText { dest: Reg, content: Reg },
    /// Set attribute on node
    SetAttr { node: Reg, name: String, value: Reg },
    /// Remove attribute from node
    RemoveAttr { node: Reg, name: String },
    /// Add class to node
    AddClass { node: Reg, class: String },
    /// Remove class from node
    RemoveClass { node: Reg, class: String },
    /// Append child to parent
    AppendChild { parent: Reg, child: Reg },
    /// Insert child at index
    InsertChild { parent: Reg, index: Reg, child: Reg },
    /// Remove child from parent
    RemoveChild { parent: Reg, child: Reg },

    // Control flow helpers
    /// Evaluate expression into register
    Eval { dest: Reg, expr: Expr },
    /// Compare two values
    Compare { dest: Reg, left: Reg, right: Reg },
    /// Begin iteration over collection
    IterBegin { dest: Reg, iterable: Reg },
    /// Get next item from iterator (or nil if done)
    IterNext { dest: Reg, iter: Reg },
    /// Check if iterator is done
    IterDone { dest: Reg, iter: Reg },

    // Patch emission
    /// Emit a patch operation
    EmitPatch { op: PatchOpKind, args: Vec<Reg> },

    // Lookup
    /// Look up node by ID
    GetNode { dest: Reg, node_id: NodeId },
}

/// Patch operation kind for EmitPatch
#[derive(Debug, Clone)]
pub enum PatchOpKind {
    SetText,
    SetAttr,
    RemoveAttr,
    AddClass,
    RemoveClass,
    InsertChild,
    RemoveChild,
    ReplaceSubtree,
    MoveChild,
}

/// Block terminator
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Unconditional jump
    Goto(BlockId),
    /// Conditional branch
    Branch {
        condition: Reg,
        then_block: BlockId,
        else_block: BlockId,
    },
    /// Return from render
    Return,
    /// Loop back (for iteration)
    Loop {
        condition: Reg,
        body: BlockId,
        exit: BlockId,
    },
}
