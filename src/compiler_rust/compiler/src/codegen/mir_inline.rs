use std::collections::HashMap;

use crate::mir::{BlockId, CallTarget, LocalKind, MirBlock, MirFunction, MirInst, MirModule, Terminator, VReg};

pub fn inline_small_pure_functions(mir: &MirModule, functions: Vec<MirFunction>) -> Vec<MirFunction> {
    let callees: HashMap<String, MirFunction> = functions
        .iter()
        .filter(|f| is_inline_candidate(f))
        .map(|f| (f.name.clone(), f.clone()))
        .collect();

    functions
        .into_iter()
        .map(|mut caller| {
            inline_in_function(&mut caller, &callees);
            caller
        })
        .collect()
}

fn is_inline_candidate(func: &MirFunction) -> bool {
    if func.name == "main"
        || func.name.starts_with("rt_")
        || func.generator_states.is_some()
        || func.async_states.is_some()
    {
        return false;
    }
    let inst_count: usize = func.blocks.iter().map(|b| b.instructions.len()).sum();
    func.blocks.len() <= 8
        && inst_count <= 48
        && !has_back_edge(func)
        && func.blocks.iter().all(|b| {
            b.instructions.iter().all(is_supported_inline_inst) && is_supported_inline_terminator(&b.terminator)
        })
}

fn has_back_edge(func: &MirFunction) -> bool {
    let block_order: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(idx, block)| (block.id, idx))
        .collect();
    func.blocks.iter().any(|block| {
        let Some(from) = block_order.get(&block.id).copied() else {
            return false;
        };
        block
            .terminator
            .successors()
            .into_iter()
            .any(|successor| block_order.get(&successor).is_some_and(|to| *to <= from))
    })
}

fn is_supported_inline_inst(inst: &MirInst) -> bool {
    matches!(
        inst,
        MirInst::ConstInt { .. }
            | MirInst::ConstBool { .. }
            | MirInst::Copy { .. }
            | MirInst::BinOp { .. }
            | MirInst::Call { .. }
            | MirInst::MethodCallStatic { .. }
            | MirInst::LocalAddr { .. }
            | MirInst::Load { .. }
            | MirInst::Store { .. }
            | MirInst::Drop { .. }
            | MirInst::EndScope { .. }
    )
}

fn is_supported_inline_terminator(term: &Terminator) -> bool {
    matches!(
        term,
        Terminator::Return(_) | Terminator::Jump(_) | Terminator::Branch { .. }
    )
}

fn inline_in_function(caller: &mut MirFunction, callees: &HashMap<String, MirFunction>) {
    let mut index = 0;
    while index < caller.blocks.len() {
        let Some((call_pos, dest, target, args)) = tail_call_in_block(&caller.blocks[index]) else {
            index += 1;
            continue;
        };
        let Some(callee) = callees.get(target.name()) else {
            index += 1;
            continue;
        };
        if callee.name == caller.name
            || callee.params.len() != args.len()
            || call_pos + 1 != caller.blocks[index].instructions.len()
        {
            index += 1;
            continue;
        }
        inline_tail_call(caller, index, call_pos, dest, args, callee);
        index += 1;
    }
}

fn tail_call_in_block(block: &MirBlock) -> Option<(usize, Option<VReg>, &CallTarget, Vec<VReg>)> {
    block
        .instructions
        .iter()
        .enumerate()
        .rev()
        .find_map(|(idx, inst)| match inst {
            MirInst::Call { dest, target, args } => Some((idx, *dest, target, args.clone())),
            _ => None,
        })
}

fn inline_tail_call(
    caller: &mut MirFunction,
    block_index: usize,
    call_pos: usize,
    call_dest: Option<VReg>,
    call_args: Vec<VReg>,
    callee: &MirFunction,
) {
    let original_terminator = caller.blocks[block_index].terminator.clone();
    let continuation = caller.new_block();
    caller.block_mut(continuation).unwrap().terminator = original_terminator;

    let mut local_map = HashMap::new();
    for (idx, local) in callee.params.iter().chain(callee.locals.iter()).enumerate() {
        let new_index = caller.params.len() + caller.locals.len();
        let mut cloned = local.clone();
        cloned.kind = LocalKind::Local;
        caller.locals.push(cloned);
        local_map.insert(idx, new_index);
    }

    let mut block_map = HashMap::new();
    for block in &callee.blocks {
        block_map.insert(block.id, caller.new_block());
    }

    let mut vreg_map = HashMap::new();
    for block in &callee.blocks {
        let new_block = block_map[&block.id];
        let mut instructions = Vec::new();
        if block.id == callee.entry_block {
            for (idx, arg) in call_args.iter().copied().enumerate() {
                let addr = caller.new_vreg();
                instructions.push(MirInst::LocalAddr {
                    dest: addr,
                    local_index: local_map[&idx],
                });
                instructions.push(MirInst::Store {
                    addr,
                    value: arg,
                    ty: callee.params[idx].ty,
                });
            }
        }
        remap_instructions(
            caller,
            &block.instructions,
            &mut instructions,
            &mut vreg_map,
            &local_map,
            &call_args,
        );
        let terminator = remap_terminator(
            caller,
            &mut instructions,
            &block.terminator,
            &mut vreg_map,
            &block_map,
            call_dest,
            continuation,
        );
        let target = caller.block_mut(new_block).unwrap();
        target.instructions = instructions;
        target.terminator = terminator;
    }

    let entry = block_map[&callee.entry_block];
    let block = &mut caller.blocks[block_index];
    block.instructions.truncate(call_pos);
    block.terminator = Terminator::Jump(entry);
}

fn remap_instructions(
    caller: &mut MirFunction,
    source: &[MirInst],
    out: &mut Vec<MirInst>,
    vreg_map: &mut HashMap<VReg, VReg>,
    local_map: &HashMap<usize, usize>,
    call_args: &[VReg],
) {
    let mut index = 0;
    while index < source.len() {
        if let Some(inst) = remap_param_load(caller, source, index, vreg_map, call_args) {
            out.push(inst);
            index += 2;
            continue;
        }
        out.push(remap_inst(caller, &source[index], vreg_map, local_map));
        index += 1;
    }
}

fn remap_param_load(
    caller: &mut MirFunction,
    source: &[MirInst],
    index: usize,
    vreg_map: &mut HashMap<VReg, VReg>,
    call_args: &[VReg],
) -> Option<MirInst> {
    let MirInst::LocalAddr {
        dest: addr,
        local_index,
    } = source.get(index)?
    else {
        return None;
    };
    let Some(arg) = call_args.get(*local_index).copied() else {
        return None;
    };
    let MirInst::Load {
        dest, addr: load_addr, ..
    } = source.get(index + 1)?
    else {
        return None;
    };
    if load_addr != addr {
        return None;
    }
    Some(MirInst::Copy {
        dest: remap_vreg(caller, *dest, vreg_map),
        src: arg,
    })
}

fn remap_inst(
    caller: &mut MirFunction,
    inst: &MirInst,
    vreg_map: &mut HashMap<VReg, VReg>,
    local_map: &HashMap<usize, usize>,
) -> MirInst {
    match inst {
        MirInst::ConstInt { dest, value } => MirInst::ConstInt {
            dest: remap_vreg(caller, *dest, vreg_map),
            value: *value,
        },
        MirInst::ConstBool { dest, value } => MirInst::ConstBool {
            dest: remap_vreg(caller, *dest, vreg_map),
            value: *value,
        },
        MirInst::Copy { dest, src } => MirInst::Copy {
            dest: remap_vreg(caller, *dest, vreg_map),
            src: remap_vreg(caller, *src, vreg_map),
        },
        MirInst::BinOp { dest, op, left, right } => MirInst::BinOp {
            dest: remap_vreg(caller, *dest, vreg_map),
            op: *op,
            left: remap_vreg(caller, *left, vreg_map),
            right: remap_vreg(caller, *right, vreg_map),
        },
        MirInst::Call { dest, target, args } => MirInst::Call {
            dest: dest.map(|v| remap_vreg(caller, v, vreg_map)),
            target: target.clone(),
            args: args.iter().map(|v| remap_vreg(caller, *v, vreg_map)).collect(),
        },
        MirInst::MethodCallStatic {
            dest,
            receiver,
            func_name,
            args,
        } => MirInst::MethodCallStatic {
            dest: dest.map(|v| remap_vreg(caller, v, vreg_map)),
            receiver: remap_vreg(caller, *receiver, vreg_map),
            func_name: func_name.clone(),
            args: args.iter().map(|v| remap_vreg(caller, *v, vreg_map)).collect(),
        },
        MirInst::LocalAddr { dest, local_index } => MirInst::LocalAddr {
            dest: remap_vreg(caller, *dest, vreg_map),
            local_index: local_map[local_index],
        },
        MirInst::Load { dest, addr, ty } => MirInst::Load {
            dest: remap_vreg(caller, *dest, vreg_map),
            addr: remap_vreg(caller, *addr, vreg_map),
            ty: *ty,
        },
        MirInst::Store { addr, value, ty } => MirInst::Store {
            addr: remap_vreg(caller, *addr, vreg_map),
            value: remap_vreg(caller, *value, vreg_map),
            ty: *ty,
        },
        MirInst::Drop { value, ty } => MirInst::Drop {
            value: remap_vreg(caller, *value, vreg_map),
            ty: *ty,
        },
        MirInst::EndScope { local_index } => MirInst::EndScope {
            local_index: local_map[local_index],
        },
        _ => unreachable!("unsupported inline instruction"),
    }
}

fn remap_terminator(
    caller: &mut MirFunction,
    instructions: &mut Vec<MirInst>,
    term: &Terminator,
    vreg_map: &mut HashMap<VReg, VReg>,
    block_map: &HashMap<BlockId, BlockId>,
    call_dest: Option<VReg>,
    continuation: BlockId,
) -> Terminator {
    match term {
        Terminator::Return(Some(v)) => {
            if let Some(dest) = call_dest {
                let src = remap_vreg(caller, *v, vreg_map);
                instructions.push(MirInst::Copy { dest, src });
            }
            Terminator::Jump(continuation)
        }
        Terminator::Return(None) => Terminator::Jump(continuation),
        Terminator::Jump(target) => Terminator::Jump(block_map[target]),
        Terminator::Branch {
            cond,
            then_block,
            else_block,
        } => Terminator::Branch {
            cond: remap_vreg(caller, *cond, vreg_map),
            then_block: block_map[then_block],
            else_block: block_map[else_block],
        },
        _ => unreachable!("unsupported inline terminator"),
    }
}

fn remap_vreg(caller: &mut MirFunction, source: VReg, map: &mut HashMap<VReg, VReg>) -> VReg {
    *map.entry(source).or_insert_with(|| caller.new_vreg())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::TypeId;
    use crate::mir::MirLocal;
    use simple_parser::ast::Visibility;

    #[test]
    fn inlines_small_tail_call_and_removes_call_inst() {
        let mut callee = MirFunction::new("tiny".to_string(), TypeId::I64, Visibility::Private);
        callee.params.push(MirLocal {
            name: "x".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        let addr = callee.new_vreg();
        let loaded = callee.new_vreg();
        callee.blocks[0].instructions.push(MirInst::LocalAddr {
            dest: addr,
            local_index: 0,
        });
        callee.blocks[0].instructions.push(MirInst::Load {
            dest: loaded,
            addr,
            ty: TypeId::I64,
        });
        callee.blocks[0].terminator = Terminator::Return(Some(loaded));

        let mut caller = MirFunction::new("caller".to_string(), TypeId::I64, Visibility::Private);
        let arg = caller.new_vreg();
        let result = caller.new_vreg();
        caller.blocks[0]
            .instructions
            .push(MirInst::ConstInt { dest: arg, value: 7 });
        caller.blocks[0].instructions.push(MirInst::Call {
            dest: Some(result),
            target: CallTarget::from_name("tiny"),
            args: vec![arg],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(result));

        let mut module = MirModule::new();
        module.functions.push(callee);
        module.functions.push(caller);

        let functions = inline_small_pure_functions(&module, module.functions.clone());
        let inlined = functions.iter().find(|f| f.name == "caller").unwrap();

        assert!(inlined.blocks.iter().all(|block| {
            block
                .instructions
                .iter()
                .all(|inst| !matches!(inst, MirInst::Call { target, .. } if target.name() == "tiny"))
        }));
        assert!(inlined.blocks.len() > 1);
        assert!(inlined
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .all(|inst| !matches!(inst, MirInst::Load { .. })));
    }

    #[test]
    fn does_not_inline_loop_callees_without_licm() {
        let mut callee = MirFunction::new("looping".to_string(), TypeId::I64, Visibility::Private);
        let counter = callee.new_vreg();
        let one = callee.new_vreg();
        let next = callee.new_vreg();
        let loop_block = callee.new_block();
        callee.blocks[0].instructions.push(MirInst::ConstInt {
            dest: counter,
            value: 0,
        });
        callee.blocks[0].terminator = Terminator::Jump(loop_block);
        callee
            .block_mut(loop_block)
            .unwrap()
            .instructions
            .push(MirInst::ConstInt { dest: one, value: 1 });
        callee.block_mut(loop_block).unwrap().instructions.push(MirInst::BinOp {
            dest: next,
            op: crate::hir::BinOp::Add,
            left: counter,
            right: one,
        });
        callee.block_mut(loop_block).unwrap().terminator = Terminator::Jump(loop_block);

        let mut caller = MirFunction::new("caller".to_string(), TypeId::I64, Visibility::Private);
        let result = caller.new_vreg();
        caller.blocks[0].instructions.push(MirInst::Call {
            dest: Some(result),
            target: CallTarget::from_name("looping"),
            args: vec![],
        });
        caller.blocks[0].terminator = Terminator::Return(Some(result));

        let mut module = MirModule::new();
        module.functions.push(callee);
        module.functions.push(caller);

        let functions = inline_small_pure_functions(&module, module.functions.clone());
        let inlined = functions.iter().find(|f| f.name == "caller").unwrap();

        assert!(inlined.blocks.iter().any(|block| {
            block
                .instructions
                .iter()
                .any(|inst| matches!(inst, MirInst::Call { target, .. } if target.name() == "looping"))
        }));
    }
}
