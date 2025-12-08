use crate::hir::{TypeId, BinOp, UnaryOp};

/// Basic block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

/// Virtual register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

/// MIR instruction
#[derive(Debug, Clone, PartialEq)]
pub enum MirInst {
    /// Load constant integer
    ConstInt { dest: VReg, value: i64 },

    /// Load constant float
    ConstFloat { dest: VReg, value: f64 },

    /// Load constant bool
    ConstBool { dest: VReg, value: bool },

    /// Copy value from one register to another
    Copy { dest: VReg, src: VReg },

    /// Binary operation
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg },

    /// Unary operation
    UnaryOp { dest: VReg, op: UnaryOp, operand: VReg },

    /// Function call
    Call { dest: Option<VReg>, func: String, args: Vec<VReg> },

    /// Load from memory
    Load { dest: VReg, addr: VReg, ty: TypeId },

    /// Store to memory
    Store { addr: VReg, value: VReg, ty: TypeId },

    /// Get address of local variable
    LocalAddr { dest: VReg, local_index: usize },

    /// Get element pointer (for arrays/structs)
    GetElementPtr { dest: VReg, base: VReg, index: VReg },
}

/// Block terminator
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Return from function
    Return(Option<VReg>),

    /// Unconditional jump
    Jump(BlockId),

    /// Conditional branch
    Branch { cond: VReg, then_block: BlockId, else_block: BlockId },

    /// Unreachable (after infinite loop, etc.)
    Unreachable,
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
}

/// Local variable in MIR function
#[derive(Debug, Clone)]
pub struct MirLocal {
    pub name: String,
    pub ty: TypeId,
    pub is_arg: bool,
}

/// MIR function
#[derive(Debug, Clone)]
pub struct MirFunction {
    pub name: String,
    pub params: Vec<MirLocal>,
    pub locals: Vec<MirLocal>,
    pub return_type: TypeId,
    pub blocks: Vec<MirBlock>,
    pub entry_block: BlockId,
    pub is_public: bool,
    next_vreg: u32,
    next_block: u32,
}

impl MirFunction {
    pub fn new(name: String, return_type: TypeId, is_public: bool) -> Self {
        let entry = MirBlock::new(BlockId(0));
        Self {
            name,
            params: Vec::new(),
            locals: Vec::new(),
            return_type,
            blocks: vec![entry],
            entry_block: BlockId(0),
            is_public,
            next_vreg: 0,
            next_block: 1,
        }
    }

    pub fn new_vreg(&mut self) -> VReg {
        let reg = VReg(self.next_vreg);
        self.next_vreg += 1;
        reg
    }

    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.blocks.push(MirBlock::new(id));
        id
    }

    pub fn block(&self, id: BlockId) -> Option<&MirBlock> {
        self.blocks.iter().find(|b| b.id == id)
    }

    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut MirBlock> {
        self.blocks.iter_mut().find(|b| b.id == id)
    }
}

/// MIR module
#[derive(Debug)]
pub struct MirModule {
    pub name: Option<String>,
    pub functions: Vec<MirFunction>,
}

impl MirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            functions: Vec::new(),
        }
    }
}

impl Default for MirModule {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mir_function_creation() {
        let func = MirFunction::new("test".to_string(), TypeId::VOID, false);
        assert_eq!(func.name, "test");
        assert_eq!(func.blocks.len(), 1);
        assert_eq!(func.entry_block, BlockId(0));
    }

    #[test]
    fn test_vreg_allocation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, false);

        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        assert_eq!(r0, VReg(0));
        assert_eq!(r1, VReg(1));
        assert_eq!(r2, VReg(2));
    }

    #[test]
    fn test_block_creation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, false);

        let b1 = func.new_block();
        let b2 = func.new_block();

        assert_eq!(b1, BlockId(1));
        assert_eq!(b2, BlockId(2));
        assert_eq!(func.blocks.len(), 3);
    }

    #[test]
    fn test_mir_instructions() {
        let mut func = MirFunction::new("add".to_string(), TypeId::I64, true);

        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt { dest: r0, value: 1 });
        entry.instructions.push(MirInst::ConstInt { dest: r1, value: 2 });
        entry.instructions.push(MirInst::BinOp {
            dest: r2,
            op: BinOp::Add,
            left: r0,
            right: r1
        });
        entry.terminator = Terminator::Return(Some(r2));

        assert_eq!(entry.instructions.len(), 3);
    }
}
