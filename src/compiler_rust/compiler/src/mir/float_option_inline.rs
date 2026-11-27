//! Inline (tag, bits) layout for typed `f64?` / `Option<f64>` locals.
//!
//! Owner decision 2026-11-27: a typed float optional is an inline tag plus the
//! exact 64-bit payload, with no heap allocation per `Some`. Every MIR value is
//! one word and no 64-bit encoding holds every f64 plus None, so the pair
//! cannot ride in one vreg. This pass gives each typed `f64?` LOCAL two hidden
//! locals instead of its one-word slot:
//!
//! - `tag: i64` — `0` nil, `4` the `Option::None` enum, `1` `Some` as the
//!   raw-bits enum (explicit typed `Some(x)`), `2` `Some` as a flat boxed
//!   float (`return x` into an `f64?` slot), `3` `Some` enum over a boxed
//!   float (generic producers). Presence is `(tag & 3) != 0`; the sub-kinds
//!   only record which one-word form to rebuild when the value escapes.
//! - `bits: f64` — the exact IEEE-754 value.
//!
//! Rule: default boxed, allowlist inline. A read of such a local stays a pair
//! only while every consumer of that read is one of the typed readers below;
//! any other consumer (an erased `any`/generic slot, a struct field or array
//! element store, a closure capture, a call argument, `return`, dynamic method
//! dispatch, an instruction this pass does not know) gets the one-word form
//! back from `rt_option_float_pack`. A missed site therefore costs an
//! allocation, never a raw f64 read as a `RuntimeValue`. A local with such a
//! read also keeps a `word` slot holding that form, built at every store (the
//! `Some` / flat float the one-word slot stored, or the very word that came
//! in), so the box has the lifetime it had before this pass and a value is
//! boxed once per assignment. Only locals with no escaping read never box.
//!
//! Typed readers (no runtime call, no allocation):
//! `rt_is_some` / `rt_is_none` (also of the `rt_unwrap_or_self` payload, where
//! the old second probe took the nil-word denormal, bits == 3, for None),
//! `rt_option_float_bits`, the raw-bits self-cast of the payload, and a store
//! into another pair local.
//!
//! Typed producers stored into a pair local: `Some(x)` (marked by the lowering
//! with an F64 self-cast of the payload), a flat `BoxFloat`, `nil`, `None`,
//! another pair. Any other word is unpacked once with `rt_option_float_tag` +
//! `rt_option_float_bits` (two calls, no allocation).
//!
//! One erased reader gets the payload as a boxed float (`tag | 8`) instead of
//! the raw bits the one-word enum handed it: a `?` payload stored into an
//! `any` slot. (`.unwrap_or(d)` on a typed local is lowered as a typed
//! coalesce in HIR and never reaches a box.)
//! seed_jit_f64_option_unwrap_or_expect_try_readers_lossy_2026-11-27
//!
//! Function signatures, struct fields, array elements and closure captures keep
//! the one-word form, so there is no ABI change. `f32?` is left alone.
//! seed_typed_f64_option_some_heap_allocates_per_some_never_released_2026-11-27

use std::collections::{HashMap, HashSet};

use super::effects::{CallTarget, LocalKind};
use super::function::{MirFunction, MirLocal};
use super::instructions::{MirInst, VReg};
use crate::hir::{BinOp, HirType, TypeId, TypeRegistry};

/// What the pass did, for tracing and tests.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct FloatOptionInlineStats {
    /// Typed `f64?` locals replaced by a (tag, bits) pair.
    pub locals_inlined: usize,
    /// Reads that still hand the one-word form to an unknown consumer.
    pub reads_boxed: usize,
    /// `Some` / flat-float / `None` allocations removed.
    pub producers_removed: usize,
}

impl FloatOptionInlineStats {
    fn merge(&mut self, other: FloatOptionInlineStats) {
        self.locals_inlined += other.locals_inlined;
        self.reads_boxed += other.reads_boxed;
        self.producers_removed += other.producers_removed;
    }
}

pub(crate) fn disabled() -> bool {
    matches!(
        std::env::var("SIMPLE_NO_F64_OPTION_INLINE").as_deref(),
        Ok("1") | Ok("true")
    )
}

/// `ty` is a source-level optional (`f64?`) or `Option<f64>`.
pub fn is_f64_option_type(registry: &TypeRegistry, ty: TypeId) -> bool {
    if registry.optional_inner(ty) == Some(TypeId::F64) {
        return true;
    }
    match registry.get(ty) {
        Some(HirType::Enum { name, variants, .. }) if name == "Option" => variants
            .iter()
            .any(|(variant, payload)| variant == "Some" && payload.as_deref() == Some(&[TypeId::F64][..])),
        _ => false,
    }
}

/// Run the rewrite over every function in a module.
pub fn apply_float_option_inline_to_module(
    functions: &mut [MirFunction],
    registry: &TypeRegistry,
) -> FloatOptionInlineStats {
    let mut stats = FloatOptionInlineStats::default();
    if disabled() {
        return stats;
    }
    for func in functions.iter_mut() {
        stats.merge(apply_float_option_inline(func, registry));
    }
    stats
}

fn is_presence_probe(name: &str) -> bool {
    matches!(name, "rt_is_some" | "rt_is_none")
}

fn call(dest: VReg, name: &str, args: Vec<VReg>) -> MirInst {
    MirInst::Call {
        dest: Some(dest),
        target: CallTarget::from_name(name),
        args,
    }
}

/// Address vreg of a hidden local, emitted once per block.
fn hidden_addr(func: &mut MirFunction, out: &mut Vec<MirInst>, addrs: &mut HashMap<usize, VReg>, local: usize) -> VReg {
    *addrs.entry(local).or_insert_with(|| {
        let dest = func.new_vreg();
        out.push(MirInst::LocalAddr {
            dest,
            local_index: local,
        });
        dest
    })
}

fn const_int(func: &mut MirFunction, out: &mut Vec<MirInst>, value: i64) -> VReg {
    let dest = func.new_vreg();
    out.push(MirInst::ConstInt { dest, value });
    dest
}

/// `tag | 8`: ask `rt_option_float_pack` for the erased payload form (a boxed
/// float, or nil) instead of the one-word optional.
fn erased_tag(func: &mut MirFunction, out: &mut Vec<MirInst>, tag: VReg) -> VReg {
    let flag = const_int(func, out, 8);
    let erased = func.new_vreg();
    out.push(MirInst::BinOp {
        dest: erased,
        op: BinOp::BitOr,
        left: tag,
        right: flag,
    });
    erased
}

/// What a pass-relevant vreg was defined by.
#[derive(Clone, Copy)]
enum Def {
    /// `Load` through this address vreg.
    Load(VReg),
    /// `OptionSome` of this payload.
    Some(VReg),
    /// `BoxFloat` of this float.
    BoxFloat(VReg),
    /// The nil word.
    Nil,
    /// `OptionNone`.
    NoneEnum,
    /// An F64 self-cast: the lowering's mark on a typed `Some` payload.
    F64Cast,
    /// `rt_unwrap_or_self` of this vreg.
    Payload(VReg),
}

/// Map keyed by the (dense, small) vreg number: the analysis touches every
/// instruction of a function with an `f64?` local, where hashing dominated.
struct Dense<T: Copy>(Vec<Option<T>>);

impl<T: Copy> Dense<T> {
    fn new(len: usize) -> Self {
        Dense(vec![None; len])
    }

    fn insert(&mut self, v: VReg, value: T) -> bool {
        match self.0.get_mut(v.0 as usize) {
            Some(slot) => slot.replace(value).is_none(),
            None => false,
        }
    }

    fn get(&self, v: &VReg) -> Option<T> {
        self.0.get(v.0 as usize).copied().flatten()
    }

    fn iter(&self) -> impl Iterator<Item = (VReg, T)> + '_ {
        self.0
            .iter()
            .enumerate()
            .filter_map(|(i, slot)| slot.map(|value| (VReg(i as u32), value)))
    }
}

/// Which reads and payloads keep which form.
#[derive(Default)]
struct Forms {
    /// Payloads with a consumer that is not a typed reader.
    kept_payload: HashSet<VReg>,
    /// Kept payloads handed over as a boxed float (`any` stores only).
    erased_payload: HashSet<VReg>,
    /// Reads with a consumer that needs the one-word form.
    needs_box: HashSet<VReg>,
}

/// Run the rewrite over one function.
pub fn apply_float_option_inline(func: &mut MirFunction, registry: &TypeRegistry) -> FloatOptionInlineStats {
    let mut stats = FloatOptionInlineStats::default();
    if disabled()
        || func.blocks.is_empty()
        || func.is_generic_template
        || !func.outlined_bodies.is_empty()
        || func.generator_states.is_some()
        || func.async_states.is_some()
    {
        return stats;
    }

    // Candidate locals: declared (non-parameter) locals typed `f64?`.
    let param_count = func.params.len();
    let declared = param_count + func.locals.len();
    let mut candidates: HashSet<usize> = func
        .locals
        .iter()
        .enumerate()
        .filter(|(_, local)| !local.is_ghost && is_f64_option_type(registry, local.ty))
        .map(|(i, _)| param_count + i)
        .collect();
    if candidates.is_empty() {
        return stats;
    }

    // One scan: definitions, address vregs, the highest local index in use.
    let vreg_bound = func.new_vreg().0 as usize;
    let mut defined: Dense<()> = Dense::new(vreg_bound);
    let mut redefined = false;
    let mut def_kind: Dense<Def> = Dense::new(vreg_bound);
    let mut addr_local: Dense<usize> = Dense::new(vreg_bound);
    let mut max_local_used = 0usize;
    for inst in func.blocks.iter().flat_map(|b| b.instructions.iter()) {
        for d in inst.defs() {
            redefined |= !defined.insert(d, ());
        }
        match inst {
            MirInst::LocalAddr { dest, local_index } => {
                addr_local.insert(*dest, *local_index);
                max_local_used = max_local_used.max(*local_index + 1);
            }
            MirInst::Load { dest, addr, .. } => {
                def_kind.insert(*dest, Def::Load(*addr));
            }
            MirInst::OptionSome { dest, value } => {
                def_kind.insert(*dest, Def::Some(*value));
            }
            MirInst::BoxFloat { dest, value } => {
                def_kind.insert(*dest, Def::BoxFloat(*value));
            }
            MirInst::ConstInt { dest, value: 3 } => {
                def_kind.insert(*dest, Def::Nil);
            }
            MirInst::OptionNone { dest } => {
                def_kind.insert(*dest, Def::NoneEnum);
            }
            MirInst::Cast {
                dest,
                from_ty: TypeId::F64,
                to_ty: TypeId::F64,
                ..
            } => {
                def_kind.insert(*dest, Def::F64Cast);
            }
            MirInst::Call {
                dest: Some(dest),
                target,
                args,
            } if args.len() == 1 && target.name() == "rt_unwrap_or_self" => {
                def_kind.insert(*dest, Def::Payload(args[0]));
            }
            MirInst::EndScope { local_index, .. } => {
                candidates.remove(local_index);
            }
            // Outlined bodies (future / actor / generator) and suspension
            // points move this function's locals into a frame the pass does
            // not model.
            MirInst::FutureCreate { .. }
            | MirInst::ActorSpawn { .. }
            | MirInst::GeneratorCreate { .. }
            | MirInst::Yield { .. }
            | MirInst::Await { .. } => {
                return stats;
            }
            _ => {}
        }
    }
    // The rewrite relies on single definitions, and on every local index
    // naming a declared local (an inferred implicit slot would be renumbered
    // by the locals appended below; see `mir::string_accum`).
    if redefined || max_local_used > declared {
        return stats;
    }
    drop(defined);

    // Escapes. A candidate's address may only feed `Load`/`Store` as the
    // address. A lambda body is outlined after this pass and reads its captures
    // through the PARENT's local index (`codegen::shared` infers the binding
    // from the `LocalAddr` + `Load` that feeds each capture), so a captured
    // local and a lambda parameter keep the one-word slot.
    let mut escaped: Vec<usize> = Vec::new();
    {
        let mut escape = |v: &VReg| {
            if let Some(local) = addr_local.get(v) {
                escaped.push(local);
            }
        };
        for block in &func.blocks {
            for inst in &block.instructions {
                match inst {
                    MirInst::LocalAddr { .. } | MirInst::Load { .. } => {}
                    MirInst::Store { value, .. } => escape(value),
                    MirInst::ClosureCreate {
                        captures,
                        lambda_params,
                        ..
                    } => {
                        for capture in captures {
                            escape(capture);
                            if let Some(Def::Load(addr)) = def_kind.get(capture) {
                                escape(&addr);
                            }
                        }
                        for param in lambda_params {
                            candidates.remove(&param.local_index);
                        }
                    }
                    other => other.uses().iter().for_each(&mut escape),
                }
            }
            block.terminator.uses().iter().for_each(&mut escape);
        }
    }
    for local in &escaped {
        candidates.remove(local);
    }
    if candidates.is_empty() {
        return stats;
    }
    let is_candidate_addr = |v: &VReg| addr_local.get(v).is_some_and(|l| candidates.contains(&l));

    // Reads of a pair local, and the `rt_unwrap_or_self` payloads of such reads.
    let mut pair_local: HashMap<VReg, usize> = HashMap::new();
    for (dest, kind) in def_kind.iter() {
        if let Def::Load(addr) = kind {
            if let Some(local) = addr_local.get(&addr).filter(|l| candidates.contains(l)) {
                pair_local.insert(dest, local);
            }
        }
    }
    let mut payload_of: HashMap<VReg, VReg> = HashMap::new();
    for (dest, kind) in def_kind.iter() {
        if let Def::Payload(read) = kind {
            if pair_local.contains_key(&read) {
                payload_of.insert(dest, read);
            }
        }
    }

    let forms = {
        // Only instructions that use a read or a payload matter from here on.
        let relevant = |v: &VReg| pair_local.contains_key(v) || payload_of.contains_key(v);
        let mut touching: Vec<&MirInst> = Vec::new();
        let mut terminator_uses: Vec<VReg> = Vec::new();
        for block in &func.blocks {
            for inst in &block.instructions {
                if inst.uses().iter().any(relevant) {
                    touching.push(inst);
                }
            }
            terminator_uses.extend(block.terminator.uses().into_iter().filter(relevant));
        }
        let mut forms = Forms::default();

        // A payload stays inline only if every use is a typed reader.
        let payload_aware = |inst: &MirInst| match inst {
            MirInst::Call { target, args, .. } => is_presence_probe(target.name()) && args.len() == 1,
            MirInst::Cast { from_ty, to_ty, .. } => *from_ty == TypeId::F64 && *to_ty == TypeId::F64,
            _ => false,
        };
        for &inst in &touching {
            if !payload_aware(inst) {
                forms
                    .kept_payload
                    .extend(inst.uses().into_iter().filter(|u| payload_of.contains_key(u)));
            }
        }
        forms
            .kept_payload
            .extend(terminator_uses.iter().copied().filter(|u| payload_of.contains_key(u)));

        // A kept payload whose every use is a store into an erased (`any`)
        // slot (`val v = c?` where HIR lost the payload type) is handed over
        // as a boxed float, the form an erased consumer decodes exactly,
        // instead of the raw bits of the old `rt_unwrap_or_self` result.
        forms.erased_payload = forms.kept_payload.clone();
        for &inst in &touching {
            let allowed = payload_aware(inst)
                || matches!(inst, MirInst::Store { addr, ty, .. }
                    if *ty == TypeId::ANY && !payload_of.contains_key(addr));
            if !allowed {
                for u in inst.uses() {
                    forms.erased_payload.remove(&u);
                }
            }
        }
        for u in &terminator_uses {
            forms.erased_payload.remove(u);
        }

        // A read needs the one-word form if any use is not a typed reader.
        let read_aware = |inst: &MirInst, forms: &Forms| match inst {
            MirInst::Store { addr, .. } => is_candidate_addr(addr),
            MirInst::Call { dest, target, args } if args.len() == 1 => match target.name() {
                "rt_is_some" | "rt_is_none" | "rt_option_float_bits" => true,
                "rt_unwrap_or_self" => dest.map_or(true, |d| {
                    !forms.kept_payload.contains(&d) || forms.erased_payload.contains(&d)
                }),
                _ => false,
            },
            _ => false,
        };
        let mut needs_box: HashSet<VReg> = HashSet::new();
        for &inst in &touching {
            if !read_aware(inst, &forms) {
                needs_box.extend(inst.uses().into_iter().filter(|u| pair_local.contains_key(u)));
            }
        }
        needs_box.extend(terminator_uses.iter().copied().filter(|u| pair_local.contains_key(u)));

        // A copy into a local that keeps a word carries the source's word (the
        // one-word slot copied the word, it did not box again), so the read
        // that feeds such a copy is an escaping read of its own local.
        let copies: Vec<(usize, VReg)> = touching
            .iter()
            .filter_map(|inst| match inst {
                MirInst::Store { addr, value, .. } if is_candidate_addr(addr) && pair_local.contains_key(value) => {
                    Some((addr_local.get(addr).unwrap(), *value))
                }
                _ => None,
            })
            .collect();
        loop {
            let cached: HashSet<usize> = needs_box.iter().map(|read| pair_local[read]).collect();
            let before = needs_box.len();
            needs_box.extend(
                copies
                    .iter()
                    .filter(|(dst, _)| cached.contains(dst))
                    .map(|(_, read)| *read),
            );
            if needs_box.len() == before {
                break;
            }
        }

        forms.needs_box = needs_box;
        forms
    };

    // Hidden locals: (tag, bits) per candidate, appended past every declared
    // one. A candidate with an escaping read gets a third, `word`: the one-word
    // form of its current value, built AT THE STORE like the one-word slot it
    // replaces (a one-word store keeps that very word). Boxing at the first
    // escaping read instead would tie the box to whatever transient scope is
    // open at that read: assigned outside a scope, first read inside one, read
    // again after `rt_transient_array_scope_end` handed out a freed pointer.
    // So a value is boxed once per assignment, with the lifetime it had before
    // this pass; locals with no escaping read have no `word` and never box.
    let cached: HashSet<usize> = forms.needs_box.iter().map(|read| pair_local[read]).collect();
    let mut hidden: HashMap<usize, (usize, usize)> = HashMap::new();
    let mut word_local: HashMap<usize, usize> = HashMap::new();
    let mut ordered: Vec<usize> = candidates.iter().copied().collect();
    ordered.sort_unstable();
    for local in ordered {
        let name = func.locals[local - param_count].name.clone();
        let tag_index = param_count + func.locals.len();
        func.locals.push(MirLocal {
            name: format!("{name}$tag"),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        func.locals.push(MirLocal {
            name: format!("{name}$bits"),
            ty: TypeId::F64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        hidden.insert(local, (tag_index, tag_index + 1));
        if cached.contains(&local) {
            word_local.insert(local, param_count + func.locals.len());
            func.locals.push(MirLocal {
                name: format!("{name}$word"),
                ty: TypeId::I64,
                kind: LocalKind::Local,
                is_ghost: false,
            });
        }
    }
    stats.locals_inlined = hidden.len();
    stats.reads_boxed = forms.needs_box.len();

    // Pair vregs of every read.
    let mut pair_vregs: HashMap<VReg, (VReg, VReg)> = HashMap::new();
    let mut reads: Vec<VReg> = pair_local.keys().copied().collect();
    reads.sort_unstable_by_key(|v| v.0);
    for read in reads {
        let tag = func.new_vreg();
        let bits = func.new_vreg();
        pair_vregs.insert(read, (tag, bits));
    }

    // The pair behind a typed-reader operand: a read, or its inline payload.
    let pair_of = |v: &VReg| -> Option<(VReg, VReg)> {
        if let Some(pair) = pair_vregs.get(v) {
            return Some(*pair);
        }
        payload_of
            .get(v)
            .filter(|_| !forms.kept_payload.contains(v) || forms.erased_payload.contains(v))
            .and_then(|read| pair_vregs.get(read).copied())
    };

    let mut consumed: HashSet<VReg> = HashSet::new();
    for block_index in 0..func.blocks.len() {
        // Leave blocks that touch no pair local as they are.
        let touched = func.blocks[block_index].instructions.iter().any(|inst| match inst {
            MirInst::LocalAddr { dest, .. } => is_candidate_addr(dest),
            MirInst::Load { addr, .. } | MirInst::Store { addr, .. } => is_candidate_addr(addr),
            MirInst::Call { args, .. } => args.len() == 1 && pair_of(&args[0]).is_some(),
            MirInst::Cast { source, .. } => payload_of.contains_key(source),
            _ => false,
        });
        if !touched {
            continue;
        }
        let old = std::mem::take(&mut func.blocks[block_index].instructions);
        let mut out: Vec<MirInst> = Vec::with_capacity(old.len());
        // One address vreg per hidden local per block.
        let mut addrs: HashMap<usize, VReg> = HashMap::new();
        for inst in old {
            match &inst {
                MirInst::LocalAddr { dest, .. } if is_candidate_addr(dest) => {}
                MirInst::Load { dest, .. } if pair_vregs.contains_key(dest) => {
                    let (tag, bits) = pair_vregs[dest];
                    let (tag_local, bits_local) = hidden[&pair_local[dest]];
                    let tag_addr = hidden_addr(func, &mut out, &mut addrs, tag_local);
                    out.push(MirInst::Load {
                        dest: tag,
                        addr: tag_addr,
                        ty: TypeId::I64,
                    });
                    let bits_addr = hidden_addr(func, &mut out, &mut addrs, bits_local);
                    out.push(MirInst::Load {
                        dest: bits,
                        addr: bits_addr,
                        ty: TypeId::F64,
                    });
                    if forms.needs_box.contains(dest) {
                        // The word built at the store (a local read before
                        // any store has none: tag 0 packs to nil).
                        let word_addr = hidden_addr(func, &mut out, &mut addrs, word_local[&pair_local[dest]]);
                        let word = func.new_vreg();
                        out.push(MirInst::Load {
                            dest: word,
                            addr: word_addr,
                            ty: TypeId::I64,
                        });
                        out.push(call(*dest, "rt_option_float_pack", vec![word, tag, bits]));
                        out.push(MirInst::Store {
                            addr: word_addr,
                            value: *dest,
                            ty: TypeId::I64,
                        });
                    }
                }
                MirInst::Store { addr, value, .. } if is_candidate_addr(addr) => {
                    let local = addr_local.get(addr).unwrap();
                    let (tag_local, bits_local) = hidden[&local];
                    // The word follows the store: the stored word itself
                    // when it is a one-word form, else boxed here.
                    let mut word = None;
                    let (tag, bits) = if let Some(pair) = pair_vregs.get(value) {
                        if forms.needs_box.contains(value) {
                            word = Some(*value);
                        }
                        *pair
                    } else {
                        match def_kind.get(value) {
                            // Typed `Some(x)`: the lowering marks a native f64
                            // payload with a self-cast.
                            Some(Def::Some(payload)) if matches!(def_kind.get(&payload), Some(Def::F64Cast)) => {
                                consumed.insert(*value);
                                (const_int(func, &mut out, 1), payload)
                            }
                            Some(Def::BoxFloat(float)) => {
                                consumed.insert(*value);
                                let bits = func.new_vreg();
                                out.push(MirInst::Cast {
                                    dest: bits,
                                    source: float,
                                    from_ty: TypeId::F64,
                                    to_ty: TypeId::F64,
                                });
                                (const_int(func, &mut out, 2), bits)
                            }
                            kind @ (Some(Def::Nil) | Some(Def::NoneEnum)) => {
                                let none_enum = matches!(kind, Some(Def::NoneEnum));
                                if none_enum {
                                    consumed.insert(*value);
                                }
                                let bits = func.new_vreg();
                                out.push(MirInst::ConstFloat { dest: bits, value: 0.0 });
                                (const_int(func, &mut out, if none_enum { 4 } else { 0 }), bits)
                            }
                            // Any other one-word form: classify and read once.
                            _ => {
                                let tag = func.new_vreg();
                                let raw = func.new_vreg();
                                let bits = func.new_vreg();
                                word = Some(*value);
                                out.push(call(tag, "rt_option_float_tag", vec![*value]));
                                out.push(call(raw, "rt_option_float_bits", vec![*value]));
                                out.push(MirInst::Cast {
                                    dest: bits,
                                    source: raw,
                                    from_ty: TypeId::F64,
                                    to_ty: TypeId::F64,
                                });
                                (tag, bits)
                            }
                        }
                    };
                    // A typed producer feeding a local that keeps a word IS that
                    // word: the `Some` / flat float / `None` / nil the one-word
                    // slot stored, built where it was built before.
                    if word.is_none()
                        && word_local.contains_key(&local)
                        && matches!(
                            def_kind.get(value),
                            Some(Def::Some(_) | Def::BoxFloat(_) | Def::Nil | Def::NoneEnum)
                        )
                    {
                        word = Some(*value);
                    }
                    let tag_addr = hidden_addr(func, &mut out, &mut addrs, tag_local);
                    out.push(MirInst::Store {
                        addr: tag_addr,
                        value: tag,
                        ty: TypeId::I64,
                    });
                    let bits_addr = hidden_addr(func, &mut out, &mut addrs, bits_local);
                    out.push(MirInst::Store {
                        addr: bits_addr,
                        value: bits,
                        ty: TypeId::F64,
                    });
                    if let Some(&word_index) = word_local.get(&local) {
                        let word = match word {
                            Some(word) => word,
                            None => {
                                let none = const_int(func, &mut out, 0);
                                let boxed = func.new_vreg();
                                out.push(call(boxed, "rt_option_float_pack", vec![none, tag, bits]));
                                boxed
                            }
                        };
                        let word_addr = hidden_addr(func, &mut out, &mut addrs, word_index);
                        out.push(MirInst::Store {
                            addr: word_addr,
                            value: word,
                            ty: TypeId::I64,
                        });
                    }
                }
                MirInst::Call {
                    dest: Some(dest),
                    target,
                    args,
                } if args.len() == 1 && pair_of(&args[0]).is_some() => {
                    let (tag, bits) = pair_of(&args[0]).unwrap();
                    let is_read = pair_vregs.contains_key(&args[0]);
                    match target.name() {
                        name @ ("rt_is_some" | "rt_is_none") => {
                            // Presence is the tag alone: `(tag & 3) != 0`.
                            let mask = const_int(func, &mut out, 3);
                            let present = func.new_vreg();
                            out.push(MirInst::BinOp {
                                dest: present,
                                op: BinOp::BitAnd,
                                left: tag,
                                right: mask,
                            });
                            let zero = const_int(func, &mut out, 0);
                            out.push(MirInst::BinOp {
                                dest: *dest,
                                op: if name == "rt_is_some" { BinOp::NotEq } else { BinOp::Eq },
                                left: present,
                                right: zero,
                            });
                        }
                        "rt_option_float_bits" if is_read => {
                            out.push(MirInst::Copy { dest: *dest, src: bits });
                        }
                        "rt_unwrap_or_self" if is_read && forms.erased_payload.contains(dest) => {
                            let tag = erased_tag(func, &mut out, tag);
                            let no_word = const_int(func, &mut out, 0);
                            out.push(call(*dest, "rt_option_float_pack", vec![no_word, tag, bits]));
                        }
                        "rt_unwrap_or_self" if is_read && !forms.kept_payload.contains(dest) => {}
                        _ => out.push(inst),
                    }
                }
                MirInst::Cast {
                    dest,
                    source,
                    from_ty: TypeId::F64,
                    to_ty: TypeId::F64,
                } if payload_of.contains_key(source) && pair_of(source).is_some() => {
                    let (_, bits) = pair_of(source).unwrap();
                    out.push(MirInst::Copy { dest: *dest, src: bits });
                }
                _ => out.push(inst),
            }
        }
        out.shrink_to_fit();
        func.blocks[block_index].instructions = out;
    }

    // Drop producers whose only consumer was a pair store.
    if !consumed.is_empty() {
        let mut used: HashSet<VReg> = HashSet::new();
        for block in &func.blocks {
            for inst in &block.instructions {
                used.extend(inst.uses().into_iter().filter(|u| consumed.contains(u)));
            }
            used.extend(block.terminator.uses().into_iter().filter(|u| consumed.contains(u)));
        }
        for block in &mut func.blocks {
            block.instructions.retain(|inst| {
                let dead = match inst {
                    MirInst::OptionSome { dest, .. }
                    | MirInst::OptionNone { dest }
                    | MirInst::BoxFloat { dest, .. } => consumed.contains(dest) && !used.contains(dest),
                    _ => false,
                };
                if dead {
                    stats.producers_removed += 1;
                }
                !dead
            });
        }
    }

    stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::parse_and_lower;

    /// (`OptionSome`, `BoxFloat`, `rt_option_float_pack`, legacy runtime
    /// readers, `rt_option_float_tag`) in one function after `lower_to_mir`,
    /// which runs this pass.
    fn counts(source: &str, func_name: &str) -> (usize, usize, usize, usize, usize) {
        let hir = parse_and_lower(source);
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lowering");
        let func = mir
            .functions
            .iter()
            .find(|f| f.name == func_name || f.name.ends_with(&format!(".{func_name}")))
            .unwrap_or_else(|| panic!("function {func_name} not in MIR"));
        let (mut some, mut boxed, mut pack, mut readers, mut unpack) = (0, 0, 0, 0, 0);
        for inst in func.blocks.iter().flat_map(|b| b.instructions.iter()) {
            match inst {
                MirInst::OptionSome { .. } => some += 1,
                MirInst::BoxFloat { .. } => boxed += 1,
                MirInst::Call { target, .. } => match target.name() {
                    "rt_option_float_pack" => pack += 1,
                    "rt_is_some" | "rt_is_none" | "rt_unwrap_or_self" | "rt_option_float_bits" => readers += 1,
                    "rt_option_float_tag" => unpack += 1,
                    _ => {}
                },
                _ => {}
            }
        }
        (some, boxed, pack, readers, unpack)
    }

    const LOOP: &str = "
fn run(n: i64) -> f64:
    var acc = 0.0
    var i = 0
    while i < n:
        val c: f64? = Some(acc)
        var d: f64? = nil
        d = c
        acc = acc + (c ?? 9.0) + c.unwrap() + (d ?? 1.0)
        i = i + 1
    acc
";

    /// The measured leak: a typed local written by `Some(x)` and read by `??`
    /// and `.unwrap()` allocates nothing and calls no runtime reader.
    #[test]
    fn typed_local_some_and_readers_are_allocation_and_call_free() {
        assert_eq!(counts(LOOP, "run"), (0, 0, 0, 0, 0));
    }

    /// A flat `x` stored into an `f64?` local is inline too.
    #[test]
    fn flat_float_into_a_typed_local_is_not_boxed() {
        let src = "
fn f(x: f64) -> f64:
    val c: f64? = x
    c ?? 9.0
";
        let (some, boxed, pack, readers, unpack) = counts(src, "f");
        assert_eq!((some, boxed, pack, readers, unpack), (0, 0, 0, 0, 0));
    }

    /// Escapes keep the one-word form: a returned local is packed at the read
    /// that feeds the `return`, and a parameter is unpacked without allocating.
    #[test]
    fn escaping_read_is_packed_and_a_parameter_is_unpacked() {
        let src = "
fn keep(x: f64) -> f64?:
    val c: f64? = Some(x)
    return c

fn read(p: f64?) -> f64:
    p ?? 9.0
";
        let (some, _, pack, readers, _) = counts(src, "keep");
        assert_eq!(
            (some, pack, readers),
            (1, 1, 0),
            "the Some is built at the assignment; the escaping read hands over that word"
        );
        let (some, _, pack, readers, unpack) = counts(src, "read");
        assert_eq!((some, pack), (0, 0));
        assert_eq!(unpack, 1, "the parameter word is classified once");
        assert_eq!(readers, 1, "only rt_option_float_bits of the parameter word remains");
    }

    /// A local captured by a lambda keeps its one-word slot: the outliner binds
    /// captures through the parent's `LocalAddr` + `Load`.
    #[test]
    fn captured_local_keeps_the_one_word_slot() {
        let src = "
fn f(x: f64) -> f64:
    val c: f64? = Some(x)
    val g = \\y: (c ?? 0.0) + y
    g(1.0)
";
        let (some, ..) = counts(src, "f");
        assert_eq!(some, 1, "the captured local still holds the Option word");
    }

    /// `f32?` is out of scope and untouched.
    #[test]
    fn f32_option_is_left_alone() {
        let src = "
fn f(x: f32) -> f32:
    val c: f32? = Some(x)
    c ?? x
";
        let (some, ..) = counts(src, "f");
        assert_eq!(some, 1);
    }

    /// `.unwrap_or(d)` on a typed local is a typed coalesce: no dynamic method
    /// call, no runtime reader, no box.
    #[test]
    fn unwrap_or_on_a_typed_local_is_a_typed_coalesce() {
        let src = "
fn f(x: f64) -> f64:
    val c: f64? = Some(x)
    val u: f64 = c.unwrap_or(9.0)
    u
";
        assert_eq!(counts(src, "f"), (0, 0, 0, 0, 0));
        let hir = parse_and_lower(src);
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lowering");
        let func = mir.functions.iter().find(|f| f.name == "f").expect("f");
        let dynamic = func
            .blocks
            .iter()
            .flat_map(|b| b.instructions.iter())
            .any(|inst| matches!(inst, MirInst::MethodCallStatic { func_name, .. } if func_name == "unwrap_or"));
        assert!(!dynamic, "unwrap_or must not reach dynamic method dispatch");
    }

    /// An escaping read hands over the cached one-word form: the pack call
    /// takes the `$word` slot and its result is stored back, so the value is
    /// boxed once per assignment.
    #[test]
    fn escaping_read_goes_through_the_word_cache() {
        let src = "
fn g(c: f64?) -> f64:
    c ?? 9.0

fn f(x: f64) -> f64:
    val c: f64? = Some(x)
    g(c) + g(c)
";
        let hir = parse_and_lower(src);
        let mir = crate::mir::lower_to_mir(&hir).expect("mir lowering");
        let func = mir.functions.iter().find(|f| f.name == "f").expect("f");
        assert!(func.locals.iter().any(|l| l.name.ends_with("$word")));
        let insts: Vec<&MirInst> = func.blocks.iter().flat_map(|b| b.instructions.iter()).collect();
        let mut packs = 0;
        for (i, inst) in insts.iter().enumerate() {
            if let MirInst::Call {
                dest: Some(dest),
                target,
                args,
            } = inst
            {
                if target.name() == "rt_option_float_pack" {
                    packs += 1;
                    assert_eq!(args.len(), 3, "cached word, tag, bits");
                    assert!(
                        matches!(insts[i + 1], MirInst::Store { value, .. } if value == dest),
                        "the packed word is stored back into the cache"
                    );
                }
            }
        }
        assert_eq!(packs, 2, "one cache lookup per escaping read");
    }
}
