//! MIR function and module definitions.
//!
//! This module defines MirFunction, MirModule, and related types.

use std::collections::{HashMap, HashSet};

use simple_parser::ast::Visibility;

use crate::hir::{LayoutPhase, TypeId};

use super::blocks::MirBlock;
use super::effects::{EffectSet, LocalKind};
use super::instructions::{BlockId, VReg};

/// Inferred effect from type checker for async-by-default semantics.
/// This mirrors simple_type::Effect but is defined here to avoid circular dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferredEffect {
    /// Non-suspending function, returns T directly
    Sync,
    /// May suspend, returns Promise[T]
    Async,
}

impl InferredEffect {
    /// Check if this effect is async (may suspend)
    pub fn is_async(&self) -> bool {
        matches!(self, InferredEffect::Async)
    }

    /// Check if this effect is sync (cannot suspend)
    pub fn is_sync(&self) -> bool {
        matches!(self, InferredEffect::Sync)
    }

    /// Get the name of this effect for error messages
    pub fn name(&self) -> &'static str {
        match self {
            InferredEffect::Sync => "sync",
            InferredEffect::Async => "async",
        }
    }
}

/// Local variable in MIR function
#[derive(Debug, Clone)]
pub struct MirLocal {
    pub name: String,
    pub ty: TypeId,
    pub kind: LocalKind,
    /// Ghost variable - only exists for verification, erased before codegen
    pub is_ghost: bool,
}

impl MirLocal {
    /// Check if this is a function argument/parameter.
    /// Helper for backwards compatibility.
    pub fn is_arg(&self) -> bool {
        self.kind.is_parameter()
    }
}

/// Metadata for an outlined body (actor/generator/future).
#[derive(Debug, Clone)]
pub struct OutlinedBody {
    pub name: String,
    pub live_ins: Vec<VReg>,
    pub frame_slots: Option<usize>,
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
    pub visibility: Visibility,
    /// Outlined bodies generated from body_block instructions (Actor/Generator/Future).
    /// Maps the original BlockId to metadata about the outlined function.
    pub outlined_bodies: HashMap<BlockId, OutlinedBody>,
    /// Generator lowering metadata (if this function represents a lowered generator dispatcher).
    pub generator_states: Option<Vec<crate::mir::generator::GeneratorState>>,
    pub generator_complete: Option<BlockId>,
    /// Async state machine metadata (if this function represents a lowered async dispatcher).
    pub async_states: Option<Vec<crate::mir::async_sm::AsyncState>>,
    pub async_complete: Option<BlockId>,
    /// Module path for this function (e.g., "app.domain.user")
    pub module_path: String,
    /// Attributes applied to this function (e.g., ["inject", "test"])
    pub attributes: Vec<String>,
    /// Effects declared for this function (e.g., ["io", "async"])
    pub effects: Vec<String>,
    /// Inferred effect from type checker (Sync/Async for async-by-default)
    /// Maps to simple_type::Effect enum
    pub inferred_effect: Option<InferredEffect>,
    /// Layout phase for code locality optimization.
    /// Determines which 4KB page group this function belongs to.
    pub layout_phase: LayoutPhase,
    /// Whether this function is an event loop anchor point.
    pub is_event_loop_anchor: bool,

    // Generic template metadata for .smf template storage
    /// Generic type parameter names (e.g., ["T", "U"] for fn foo<T, U>)
    pub generic_params: Vec<String>,
    /// True if this is an unspecialized generic template (should be stored in .smf)
    pub is_generic_template: bool,
    /// Base template name if this is a specialization (e.g., "identity" for "identity$Int")
    pub specialization_of: Option<String>,
    /// Type parameter bindings for specializations (e.g., T -> Int)
    pub type_bindings: HashMap<String, TypeId>,

    next_vreg: u32,
    next_block: u32,
}

impl MirFunction {
    /// Create a new MIR function with the given visibility.
    pub fn new(name: String, return_type: TypeId, visibility: Visibility) -> Self {
        let entry = MirBlock::new(BlockId(0));
        Self {
            name,
            params: Vec::new(),
            locals: Vec::new(),
            return_type,
            blocks: vec![entry],
            entry_block: BlockId(0),
            visibility,
            outlined_bodies: HashMap::new(),
            generator_states: None,
            generator_complete: None,
            async_states: None,
            async_complete: None,
            module_path: String::new(),
            attributes: Vec::new(),
            effects: Vec::new(),
            inferred_effect: None,
            layout_phase: LayoutPhase::default(),
            is_event_loop_anchor: false,
            generic_params: Vec::new(),
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            next_vreg: 0,
            next_block: 1,
        }
    }

    /// Create a new MIR function from a boolean public flag.
    /// Helper for backwards compatibility during migration.
    pub fn new_from_bool(name: String, return_type: TypeId, is_public: bool) -> Self {
        let visibility = if is_public {
            Visibility::Public
        } else {
            Visibility::Private
        };
        Self::new(name, return_type, visibility)
    }

    /// Check if this function is public.
    /// Helper for backwards compatibility.
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }

    /// Create a simple outlined function name from a base name and block id.
    pub fn outlined_name(&self, block: BlockId) -> String {
        format!("{}_outlined_{}", self.name, block.0)
    }

    /// Compute live-in set for each block using standard backward liveness.
    pub fn compute_live_ins(&self) -> HashMap<BlockId, HashSet<VReg>> {
        let mut live_in: HashMap<BlockId, HashSet<VReg>> = HashMap::new();
        let mut live_out: HashMap<BlockId, HashSet<VReg>> = HashMap::new();

        // Precompute use/def per block
        let mut block_uses: HashMap<BlockId, HashSet<VReg>> = HashMap::new();
        let mut block_defs: HashMap<BlockId, HashSet<VReg>> = HashMap::new();
        for b in &self.blocks {
            let mut uses = HashSet::new();
            let mut defs = HashSet::new();
            for inst in &b.instructions {
                if let Some(d) = inst.dest() {
                    defs.insert(d);
                }
                for u in inst.uses() {
                    if !defs.contains(&u) {
                        uses.insert(u);
                    }
                }
            }
            for u in b.terminator.uses() {
                if !defs.contains(&u) {
                    uses.insert(u);
                }
            }
            block_uses.insert(b.id, uses);
            block_defs.insert(b.id, defs);
        }

        // Initialize sets
        for b in &self.blocks {
            live_in.insert(b.id, HashSet::new());
            live_out.insert(b.id, HashSet::new());
        }

        let mut changed = true;
        while changed {
            changed = false;
            for b in &self.blocks {
                let succs = b.terminator.successors();
                let out_set = live_out.get_mut(&b.id).unwrap();
                out_set.clear();
                for s in succs {
                    if let Some(s_in) = live_in.get(&s) {
                        out_set.extend(s_in.iter().copied());
                    }
                }

                let mut new_in = block_uses[&b.id].clone();
                for reg in &live_out[&b.id] {
                    if !block_defs[&b.id].contains(reg) {
                        new_in.insert(*reg);
                    }
                }

                let current_in = live_in.get_mut(&b.id).unwrap();
                if *current_in != new_in {
                    *current_in = new_in;
                    changed = true;
                }
            }
        }

        live_in
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

    /// Keep only blocks reachable from the given entry using terminator successors.
    pub fn retain_reachable_from(&mut self, entry: BlockId) {
        let mut reachable = HashSet::new();
        let mut stack = vec![entry];
        while let Some(id) = stack.pop() {
            if !reachable.insert(id) {
                continue;
            }
            if let Some(b) = self.block(id) {
                for succ in b.terminator.successors() {
                    stack.push(succ);
                }
            }
        }
        self.blocks.retain(|b| reachable.contains(&b.id));
        self.entry_block = entry;
    }

    /// Collect all effects in this function.
    pub fn effects(&self) -> EffectSet {
        let mut set = EffectSet::new();
        for block in &self.blocks {
            set.append(&block.effects());
        }
        set
    }

    /// Check if this function is async (no blocking operations).
    pub fn is_async(&self) -> bool {
        self.effects().is_pipeline_safe()
    }

    /// Check if this function is nogc (no GC allocations).
    pub fn is_nogc(&self) -> bool {
        self.effects().is_nogc()
    }
}

/// MIR module
#[derive(Debug)]
pub struct MirModule {
    pub name: Option<String>,
    pub functions: Vec<MirFunction>,
    /// Global variables: (name, type_id, is_mutable)
    pub globals: Vec<(String, crate::hir::TypeId, bool)>,
}

impl MirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            functions: Vec::new(),
            globals: Vec::new(),
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
    use crate::hir::BinOp;
    use crate::mir::blocks::Terminator;
    use crate::mir::instructions::MirInst;

    #[test]
    fn test_mir_function_creation() {
        let func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        assert_eq!(func.name, "test");
        assert_eq!(func.blocks.len(), 1);
        assert_eq!(func.entry_block, BlockId(0));
        assert!(!func.is_public());
    }

    #[test]
    fn test_mir_function_visibility() {
        let pub_func = MirFunction::new("pub_fn".to_string(), TypeId::VOID, Visibility::Public);
        let priv_func = MirFunction::new("priv_fn".to_string(), TypeId::VOID, Visibility::Private);

        assert!(pub_func.is_public());
        assert!(!priv_func.is_public());
        assert_eq!(pub_func.visibility, Visibility::Public);
        assert_eq!(priv_func.visibility, Visibility::Private);
    }

    #[test]
    fn test_vreg_allocation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        assert_eq!(r0, VReg(0));
        assert_eq!(r1, VReg(1));
        assert_eq!(r2, VReg(2));
    }

    #[test]
    fn test_block_creation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        let b1 = func.new_block();
        let b2 = func.new_block();

        assert_eq!(b1, BlockId(1));
        assert_eq!(b2, BlockId(2));
        assert_eq!(func.blocks.len(), 3);
    }

    #[test]
    fn test_mir_instructions() {
        let mut func = MirFunction::new("add".to_string(), TypeId::I64, Visibility::Public);

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
            right: r1,
        });
        entry.terminator = Terminator::Return(Some(r2));

        assert_eq!(entry.instructions.len(), 3);
    }
}
