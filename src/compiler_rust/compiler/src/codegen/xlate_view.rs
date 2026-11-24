//! MIR->CLIF translation off the calling thread (JIT body loop).
//!
//! Translation declares functions and data objects on demand
//! (`declare_function` / `declare_data` / `define_data`) and inserts into
//! `func_ids`, so it used to need `&mut module` and ran on one thread. A
//! worker now translates against a frozen [`Snapshot`] through
//! [`XlateModule`] (a read-only `Module` view) and a `FuncIdTable` view:
//!
//! - A name the snapshot lacks gets a *provisional* id (>= [`PROVISIONAL_BASE`]).
//!   Every declaration, `define_data` and `func_ids` insert is logged as a
//!   command instead of being applied.
//! - Every name the translation looks up is logged as a read (a 64-bit hash).
//! - The calling thread takes results in function order. A result is accepted
//!   only if none of its reads was changed by a function after the snapshot;
//!   then its commands are replayed on the real module in the logged order and
//!   provisional ids in the CLIF are renamed to the real ones. The replay makes
//!   exactly the calls the serial loop makes at that point, so every
//!   FuncId/DataId, the CLIF and the machine code match the serial loop.
//! - A stale result is translated again on the calling thread (through the
//!   same view over the live state, so its mutations are still tracked).
//!
//! Lockless: workers share only immutable `Arc<Snapshot>`s and talk to the
//! calling thread over channels. The read log is per thread (`thread_local`).

use std::cell::RefCell;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use cranelift_codegen::control::ControlPlane;
use cranelift_codegen::ir::{self, Signature, UserExternalName};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::{Context, FinalizedMachReloc};
use cranelift_module::{
    DataDescription, DataId, FuncId, FuncOrDataId, Linkage, Module, ModuleDeclarations, ModuleError, ModuleResult,
};

use super::func_id_table::{qualified_tails, FuncIdTable};

/// Provisional ids start here; real modules never come close.
pub(crate) const PROVISIONAL_BASE: u32 = 1 << 30;

/// Read-hash namespaces.
const NS_FUNC_ID_KEY: u8 = 0;
const NS_FUNC_ID_TAIL: u8 = 1;
const NS_FUNC_ID_LEN: u8 = 2;
const NS_MODULE_NAME: u8 = 3;
const NS_FUNC_ID_METHOD: u8 = 4;

fn tagged_hash<Q: Hash + ?Sized>(tag: u8, key: &Q) -> u64 {
    // SipHash with fixed keys: deterministic across threads and runs.
    #[allow(deprecated)]
    let mut h = std::hash::SipHasher::new();
    h.write_u8(tag);
    key.hash(&mut h);
    h.finish()
}

pub(crate) fn func_id_key_hash<Q: Hash + ?Sized>(key: &Q) -> u64 {
    tagged_hash(NS_FUNC_ID_KEY, key)
}
pub(crate) fn func_id_tail_hash(tail: &str) -> u64 {
    tagged_hash(NS_FUNC_ID_TAIL, tail)
}
pub(crate) fn func_id_len_hash() -> u64 {
    tagged_hash(NS_FUNC_ID_LEN, "#len")
}
pub(crate) fn func_id_method_hash(method: &str) -> u64 {
    tagged_hash(NS_FUNC_ID_METHOD, method)
}

/// Every `method` for which `key` ends in `.<method>` or `_dot_<method>`
/// (what `FuncIdTable::iter_method_suffix` matches).
fn method_suffixes(key: &str) -> impl Iterator<Item = &str> + '_ {
    let dots = key.match_indices('.').map(move |(i, _)| &key[i + 1..]);
    let dot_words = key.match_indices("_dot_").map(move |(i, _)| &key[i + 5..]);
    dots.chain(dot_words)
}
fn module_name_hash(name: &str) -> u64 {
    tagged_hash(NS_MODULE_NAME, name)
}

/// What one translation read and whether it stepped outside the view.
#[derive(Default)]
pub(crate) struct XlateLog {
    pub reads: Vec<u64>,
    /// Set when the translation did something the view cannot replay
    /// (anonymous declarations, defining functions, map access through
    /// `Deref`, ...). The result must then be discarded.
    pub unsupported: Option<&'static str>,
    /// (linkage, parameter count) of provisional functions, for
    /// [`func_decl_linkage_params`].
    prov_funcs: Vec<(Linkage, usize)>,
}

thread_local! {
    static LOG: RefCell<Option<XlateLog>> = const { RefCell::new(None) };
}

pub(crate) fn begin() {
    LOG.with(|l| *l.borrow_mut() = Some(XlateLog::default()));
}

pub(crate) fn end() -> XlateLog {
    LOG.with(|l| l.borrow_mut().take()).unwrap_or_default()
}

pub(crate) fn record_read(hash: u64) {
    LOG.with(|l| {
        if let Some(log) = l.borrow_mut().as_mut() {
            log.reads.push(hash);
        }
    });
}

pub(crate) fn mark_unsupported(why: &'static str) {
    LOG.with(|l| {
        if let Some(log) = l.borrow_mut().as_mut() {
            log.unsupported.get_or_insert(why);
        }
    });
}

/// Linkage and parameter count of `id`, for translation code that inspects a
/// declaration by id. Works for provisional ids, and logs the read.
pub(crate) fn func_decl_linkage_params<M: Module>(module: &M, id: FuncId) -> (Linkage, usize) {
    if id.as_u32() >= PROVISIONAL_BASE {
        let found = LOG.with(|l| {
            l.borrow()
                .as_ref()
                .and_then(|log| log.prov_funcs.get((id.as_u32() - PROVISIONAL_BASE) as usize).copied())
        });
        return found.expect("provisional FuncId outside a translation view");
    }
    let decl = module.declarations().get_function_decl(id);
    if let Some(name) = &decl.name {
        if LOG.with(|l| l.borrow().is_some()) {
            record_read(module_name_hash(name));
        }
    }
    // A live view may have merged a new linkage into a snapshot declaration.
    let linkage = OVERRIDES.with(|o| o.borrow().get(&id).copied()).unwrap_or(decl.linkage);
    (linkage, decl.signature.params.len())
}

thread_local! {
    /// Linkages an `XlateModule` merged into snapshot function declarations
    /// (the declarations themselves are shared and frozen). Empty outside a view.
    static OVERRIDES: RefCell<HashMap<FuncId, Linkage>> = RefCell::new(HashMap::new());
}

/// Same as cranelift-module's private `Linkage::merge`.
fn merge_linkage(a: Linkage, b: Linkage) -> Linkage {
    match a {
        Linkage::Export => Linkage::Export,
        Linkage::Hidden => match b {
            Linkage::Export => Linkage::Export,
            Linkage::Preemptible => Linkage::Preemptible,
            _ => Linkage::Hidden,
        },
        Linkage::Preemptible => match b {
            Linkage::Export => Linkage::Export,
            _ => Linkage::Preemptible,
        },
        Linkage::Local => match b {
            Linkage::Export => Linkage::Export,
            Linkage::Hidden => Linkage::Hidden,
            Linkage::Preemptible => Linkage::Preemptible,
            Linkage::Local | Linkage::Import => Linkage::Local,
        },
        Linkage::Import => b,
    }
}

/// Frozen declarations + `func_ids` that workers translate against.
/// `epoch` = number of body positions already applied to the live state.
pub(crate) struct Snapshot {
    pub decls: ModuleDeclarations,
    pub func_ids: std::sync::Arc<FuncIdTable>,
    pub epoch: usize,
}

impl Snapshot {
    /// Copy `decls` (same ids: re-declared in id order) and `func_ids`.
    pub(crate) fn capture(decls: &ModuleDeclarations, func_ids: &FuncIdTable, epoch: usize) -> Self {
        let mut copy = ModuleDeclarations::default();
        for (id, d) in decls.get_functions() {
            let new_id = match &d.name {
                Some(name) => copy.declare_function(name, d.linkage, &d.signature).map(|(id, _)| id),
                None => copy.declare_anonymous_function(&d.signature),
            }
            .expect("re-declaring a declared function");
            debug_assert_eq!(new_id, id);
        }
        for (id, d) in decls.get_data_objects() {
            let new_id = match &d.name {
                Some(name) => copy.declare_data(name, d.linkage, d.writable, d.tls).map(|(id, _)| id),
                None => copy.declare_anonymous_data(d.writable, d.tls),
            }
            .expect("re-declaring a declared data object");
            debug_assert_eq!(new_id, id);
        }
        Self {
            decls: copy,
            func_ids: std::sync::Arc::new(func_ids.snapshot_clone()),
            epoch,
        }
    }
}

/// A declaration-side command logged by [`XlateModule`], replayed in order.
pub(crate) enum ModuleCmd {
    Func {
        name: String,
        linkage: Linkage,
        sig: Signature,
        result: Option<FuncId>,
    },
    Data {
        name: String,
        linkage: Linkage,
        writable: bool,
        tls: bool,
        result: Option<DataId>,
    },
    DefineData {
        id: DataId,
        desc: DataDescription,
    },
}

/// Read-only `Module` view over a declaration set for one translation.
pub(crate) struct XlateModule<'a> {
    isa: &'a dyn TargetIsa,
    decls: &'a ModuleDeclarations,
    names: HashMap<String, FuncOrDataId>,
    funcs: Vec<(Linkage, Signature)>,
    data: Vec<(Linkage, bool, bool)>,
    data_override: HashMap<DataId, (Linkage, bool)>,
    pub(crate) cmds: Vec<ModuleCmd>,
}

impl<'a> XlateModule<'a> {
    pub(crate) fn new(isa: &'a dyn TargetIsa, decls: &'a ModuleDeclarations) -> Self {
        OVERRIDES.with(|o| o.borrow_mut().clear());
        Self {
            isa,
            decls,
            names: HashMap::new(),
            funcs: Vec::new(),
            data: Vec::new(),
            data_override: HashMap::new(),
            cmds: Vec::new(),
        }
    }

    /// Name lookup for the declare methods. Not logged as a read: a
    /// declaration's outcome is re-checked against the live state before it
    /// is replayed (`replay_applies_cleanly`), so it may differ from the
    /// snapshot as long as it resolves the same way.
    fn lookup(&self, name: &str) -> Option<FuncOrDataId> {
        self.names.get(name).copied().or_else(|| self.decls.get_name(name))
    }

    fn func_linkage(&self, id: FuncId) -> Linkage {
        OVERRIDES
            .with(|o| o.borrow().get(&id).copied())
            .unwrap_or_else(|| self.decls.get_function_decl(id).linkage)
    }

    fn unsupported<T>(&self, why: &'static str) -> ModuleResult<T> {
        mark_unsupported(why);
        Err(ModuleError::Undeclared(format!("translation view: {why}")))
    }
}

impl Drop for XlateModule<'_> {
    fn drop(&mut self) {
        OVERRIDES.with(|o| o.borrow_mut().clear());
    }
}

impl Module for XlateModule<'_> {
    fn isa(&self) -> &dyn TargetIsa {
        self.isa
    }

    fn declarations(&self) -> &ModuleDeclarations {
        self.decls
    }

    fn get_name(&self, name: &str) -> Option<FuncOrDataId> {
        if let Some(id) = self.names.get(name) {
            return Some(*id);
        }
        record_read(module_name_hash(name));
        self.decls.get_name(name)
    }

    fn declare_function(&mut self, name: &str, linkage: Linkage, signature: &Signature) -> ModuleResult<FuncId> {
        let result = match self.lookup(name) {
            Some(FuncOrDataId::Func(id)) if id.as_u32() >= PROVISIONAL_BASE => {
                let slot = (id.as_u32() - PROVISIONAL_BASE) as usize;
                let entry = &mut self.funcs[slot];
                entry.0 = merge_linkage(entry.0, linkage);
                let merged = entry.0;
                let compatible = entry.1 == *signature;
                LOG.with(|l| {
                    if let Some(log) = l.borrow_mut().as_mut() {
                        log.prov_funcs[slot].0 = merged;
                    }
                });
                if compatible {
                    Ok(id)
                } else {
                    Err(ModuleError::IncompatibleSignature(
                        name.to_owned(),
                        self.funcs[slot].1.clone(),
                        signature.clone(),
                    ))
                }
            }
            Some(FuncOrDataId::Func(id)) => {
                let merged = merge_linkage(self.func_linkage(id), linkage);
                OVERRIDES.with(|o| o.borrow_mut().insert(id, merged));
                let existing = &self.decls.get_function_decl(id).signature;
                if existing == signature {
                    Ok(id)
                } else {
                    Err(ModuleError::IncompatibleSignature(
                        name.to_owned(),
                        existing.clone(),
                        signature.clone(),
                    ))
                }
            }
            Some(FuncOrDataId::Data(_)) => Err(ModuleError::IncompatibleDeclaration(name.to_owned())),
            None => {
                let id = FuncId::from_u32(PROVISIONAL_BASE + self.funcs.len() as u32);
                self.funcs.push((linkage, signature.clone()));
                LOG.with(|l| {
                    if let Some(log) = l.borrow_mut().as_mut() {
                        log.prov_funcs.push((linkage, signature.params.len()));
                    }
                });
                self.names.insert(name.to_owned(), FuncOrDataId::Func(id));
                Ok(id)
            }
        };
        self.cmds.push(ModuleCmd::Func {
            name: name.to_owned(),
            linkage,
            sig: signature.clone(),
            result: result.as_ref().ok().copied(),
        });
        result
    }

    fn declare_anonymous_function(&mut self, _signature: &Signature) -> ModuleResult<FuncId> {
        self.unsupported("anonymous function declaration")
    }

    fn declare_data(&mut self, name: &str, linkage: Linkage, writable: bool, tls: bool) -> ModuleResult<DataId> {
        let result = match self.lookup(name) {
            Some(FuncOrDataId::Data(id)) if id.as_u32() >= PROVISIONAL_BASE => {
                let entry = &mut self.data[(id.as_u32() - PROVISIONAL_BASE) as usize];
                if entry.2 != tls {
                    return self.unsupported("data declaration changes tls");
                }
                entry.0 = merge_linkage(entry.0, linkage);
                entry.1 |= writable;
                Ok(id)
            }
            Some(FuncOrDataId::Data(id)) => {
                let decl = self.decls.get_data_decl(id);
                if decl.tls != tls {
                    return self.unsupported("data declaration changes tls");
                }
                let (cur_linkage, cur_writable) =
                    self.data_override.get(&id).copied().unwrap_or((decl.linkage, decl.writable));
                self.data_override
                    .insert(id, (merge_linkage(cur_linkage, linkage), cur_writable || writable));
                Ok(id)
            }
            Some(FuncOrDataId::Func(_)) => Err(ModuleError::IncompatibleDeclaration(name.to_owned())),
            None => {
                let id = DataId::from_u32(PROVISIONAL_BASE + self.data.len() as u32);
                self.data.push((linkage, writable, tls));
                self.names.insert(name.to_owned(), FuncOrDataId::Data(id));
                Ok(id)
            }
        };
        self.cmds.push(ModuleCmd::Data {
            name: name.to_owned(),
            linkage,
            writable,
            tls,
            result: result.as_ref().ok().copied(),
        });
        result
    }

    fn declare_anonymous_data(&mut self, _writable: bool, _tls: bool) -> ModuleResult<DataId> {
        self.unsupported("anonymous data declaration")
    }

    fn define_function_with_control_plane(
        &mut self,
        _func: FuncId,
        _ctx: &mut Context,
        _ctrl_plane: &mut ControlPlane,
    ) -> ModuleResult<()> {
        self.unsupported("function definition")
    }

    fn define_function_bytes(
        &mut self,
        _func_id: FuncId,
        _func: &ir::Function,
        _alignment: u64,
        _bytes: &[u8],
        _relocs: &[FinalizedMachReloc],
    ) -> ModuleResult<()> {
        self.unsupported("function definition")
    }

    /// Logged and replayed later. The one translation caller
    /// (`declare_named_bytes`) ignores the result, so `Ok` here matches the
    /// serial path whether or not the object was already defined.
    fn define_data(&mut self, data_id: DataId, data: &DataDescription) -> ModuleResult<()> {
        if !data.function_decls.is_empty() || !data.data_decls.is_empty() {
            return self.unsupported("data object with relocations");
        }
        self.cmds.push(ModuleCmd::DefineData {
            id: data_id,
            desc: data.clone(),
        });
        Ok(())
    }

    fn declare_func_in_func(&mut self, func_id: FuncId, func: &mut ir::Function) -> ir::FuncRef {
        let (linkage, signature) = if func_id.as_u32() >= PROVISIONAL_BASE {
            let (linkage, sig) = &self.funcs[(func_id.as_u32() - PROVISIONAL_BASE) as usize];
            (*linkage, sig.clone())
        } else {
            let decl = self.decls.get_function_decl(func_id);
            if let Some(name) = &decl.name {
                record_read(module_name_hash(name));
            }
            (self.func_linkage(func_id), decl.signature.clone())
        };
        let signature = func.import_signature(signature);
        let user_name_ref = func.declare_imported_user_function(UserExternalName {
            namespace: 0,
            index: func_id.as_u32(),
        });
        func.import_function(ir::ExtFuncData {
            name: ir::ExternalName::user(user_name_ref),
            signature,
            colocated: linkage.is_final(),
        })
    }

    fn declare_data_in_func(&self, data: DataId, func: &mut ir::Function) -> ir::GlobalValue {
        let (linkage, tls) = if data.as_u32() >= PROVISIONAL_BASE {
            let (linkage, _, tls) = self.data[(data.as_u32() - PROVISIONAL_BASE) as usize];
            (linkage, tls)
        } else {
            let decl = self.decls.get_data_decl(data);
            if let Some(name) = &decl.name {
                record_read(module_name_hash(name));
            }
            let linkage = self.data_override.get(&data).map_or(decl.linkage, |o| o.0);
            (linkage, decl.tls)
        };
        let user_name_ref = func.declare_imported_user_function(UserExternalName {
            namespace: 1,
            index: data.as_u32(),
        });
        func.create_global_value(ir::GlobalValueData::Symbol {
            name: ir::ExternalName::user(user_name_ref),
            offset: ir::immediates::Imm64::new(0),
            colocated: linkage.is_final(),
            tls,
        })
    }
}

/// Provisional -> real ids after a replay.
#[derive(Default)]
pub(crate) struct Replayed {
    funcs: Vec<Option<FuncId>>,
    data: Vec<Option<DataId>>,
}

impl Replayed {
    pub(crate) fn func(&self, id: FuncId) -> FuncId {
        if id.as_u32() < PROVISIONAL_BASE {
            return id;
        }
        self.funcs
            .get((id.as_u32() - PROVISIONAL_BASE) as usize)
            .copied()
            .flatten()
            .expect("provisional FuncId was never replayed")
    }

    fn data(&self, id: DataId) -> DataId {
        if id.as_u32() < PROVISIONAL_BASE {
            return id;
        }
        self.data
            .get((id.as_u32() - PROVISIONAL_BASE) as usize)
            .copied()
            .flatten()
            .expect("provisional DataId was never replayed")
    }

    fn bind<T: Copy + PartialEq + std::fmt::Debug>(slots: &mut Vec<Option<T>>, prov: u32, real: T, name: &str) {
        let slot = (prov - PROVISIONAL_BASE) as usize;
        if slots.len() <= slot {
            slots.resize(slot + 1, None);
        }
        match slots[slot] {
            None => slots[slot] = Some(real),
            Some(bound) => assert_eq!(bound, real, "[xlate] `{name}` replayed to two different ids"),
        }
    }
}

/// Whether replaying `cmds` on `module` gives every declaration the outcome
/// the view gave it. A name the view saw as new may since have been declared
/// by an earlier function. That is fine when the existing declaration has
/// the same kind and signature (tls for data) and merging the view's linkage
/// (and writability) into it yields exactly what the view assumed: the serial
/// loop would then have produced the same id use, colocation and result.
pub(crate) fn replay_applies_cleanly<M: Module>(module: &M, cmds: &[ModuleCmd]) -> bool {
    let mut first_seen: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for cmd in cmds {
        match cmd {
            ModuleCmd::Func {
                name,
                linkage,
                sig,
                result: Some(id),
            } if id.as_u32() >= PROVISIONAL_BASE => {
                if !first_seen.insert(name) {
                    continue;
                }
                match module.get_name(name) {
                    None => {}
                    Some(FuncOrDataId::Func(live)) => {
                        let d = module.declarations().get_function_decl(live);
                        if d.signature != *sig || merge_linkage(d.linkage, *linkage) != *linkage {
                            return false;
                        }
                    }
                    Some(FuncOrDataId::Data(_)) => return false,
                }
            }
            ModuleCmd::Data {
                name,
                linkage,
                writable,
                tls,
                result: Some(id),
            } if id.as_u32() >= PROVISIONAL_BASE => {
                if !first_seen.insert(name) {
                    continue;
                }
                match module.get_name(name) {
                    None => {}
                    Some(FuncOrDataId::Data(live)) => {
                        let d = module.declarations().get_data_decl(live);
                        if d.tls != *tls || merge_linkage(d.linkage, *linkage) != *linkage || (d.writable && !*writable) {
                            return false;
                        }
                    }
                    Some(FuncOrDataId::Func(_)) => return false,
                }
            }
            _ => {}
        }
    }
    true
}

/// Replay `cmds` on the real module in order. `touch` receives the hash of
/// every module name whose declaration was created or changed.
pub(crate) fn replay<M: Module>(module: &mut M, cmds: Vec<ModuleCmd>, mut touch: impl FnMut(u64, &str)) -> Replayed {
    let mut out = Replayed::default();
    for cmd in cmds {
        match cmd {
            ModuleCmd::Func {
                name,
                linkage,
                sig,
                result,
            } => {
                let before = match module.get_name(&name) {
                    Some(FuncOrDataId::Func(id)) => Some(Some(module.declarations().get_function_decl(id).linkage)),
                    Some(FuncOrDataId::Data(_)) => Some(None),
                    None => None,
                };
                let real = module.declare_function(&name, linkage, &sig);
                match (&real, result) {
                    (Ok(real), Some(seen)) if seen.as_u32() >= PROVISIONAL_BASE => {
                        Replayed::bind(&mut out.funcs, seen.as_u32(), *real, &name)
                    }
                    (Ok(real), Some(seen)) => assert_eq!(*real, seen, "[xlate] `{name}` replayed to another id"),
                    (Err(_), None) => {}
                    _ => panic!("[xlate] replay of function `{name}` disagrees with the translation view"),
                }
                let after = match module.get_name(&name) {
                    Some(FuncOrDataId::Func(id)) => Some(Some(module.declarations().get_function_decl(id).linkage)),
                    Some(FuncOrDataId::Data(_)) => Some(None),
                    None => None,
                };
                if before != after {
                    touch(module_name_hash(&name), &name);
                }
            }
            ModuleCmd::Data {
                name,
                linkage,
                writable,
                tls,
                result,
            } => {
                let state = |module: &M| match module.get_name(&name) {
                    Some(FuncOrDataId::Data(id)) => {
                        let d = module.declarations().get_data_decl(id);
                        Some(Some((d.linkage, d.writable)))
                    }
                    Some(FuncOrDataId::Func(_)) => Some(None),
                    None => None,
                };
                let before = state(module);
                let real = module.declare_data(&name, linkage, writable, tls);
                match (&real, result) {
                    (Ok(real), Some(seen)) if seen.as_u32() >= PROVISIONAL_BASE => {
                        Replayed::bind(&mut out.data, seen.as_u32(), *real, &name)
                    }
                    (Ok(real), Some(seen)) => assert_eq!(*real, seen, "[xlate] `{name}` replayed to another id"),
                    (Err(_), None) => {}
                    _ => panic!("[xlate] replay of data `{name}` disagrees with the translation view"),
                }
                if before != state(module) {
                    touch(module_name_hash(&name), &name);
                }
            }
            ModuleCmd::DefineData { id, desc } => {
                let _ = module.define_data(out.data(id), &desc);
            }
        }
    }
    out
}

/// Replay a view's `func_ids` inserts on the live table. `touch` receives the
/// hashes of every key (and the tails / length / scan it affects) that changed.
pub(crate) fn replay_func_ids(
    table: &mut FuncIdTable,
    log: Vec<(String, FuncId, bool)>,
    ids: &Replayed,
    mut touch: impl FnMut(u64, &str),
) {
    for (key, id, or_insert) in log {
        let id = ids.func(id);
        let (changed, new_key) = if or_insert {
            if table.contains_key(key.as_str()) {
                (false, false)
            } else {
                table.insert(key.clone(), id);
                (true, true)
            }
        } else {
            let old = table.insert(key.clone(), id);
            (old != Some(id), old.is_none())
        };
        if changed {
            touch(func_id_key_hash(key.as_str()), &key);
            for tail in qualified_tails(&key) {
                touch(func_id_tail_hash(tail), tail);
            }
            if new_key {
                touch(func_id_len_hash(), "#len");
            }
            for method in method_suffixes(&key) {
                touch(func_id_method_hash(method), method);
            }
        }
    }
}

/// Rename provisional ids in `func`'s external-name table to the real ids.
pub(crate) fn remap_provisional(func: &mut ir::Function, ids: &Replayed) {
    let renames: Vec<_> = func
        .params
        .user_named_funcs()
        .iter()
        .filter(|(_, name)| name.index >= PROVISIONAL_BASE)
        .map(|(r, name)| (r, name.clone()))
        .collect();
    for (r, name) in renames {
        let index = match name.namespace {
            0 => ids.func(FuncId::from_u32(name.index)).as_u32(),
            1 => ids.data(DataId::from_u32(name.index)).as_u32(),
            other => panic!("[xlate] unexpected external-name namespace {other}"),
        };
        func.params.reset_user_func_name(
            r,
            UserExternalName {
                namespace: name.namespace,
                index,
            },
        );
    }
}

/// True when code is being translated for the JIT. `XlateModule` stands in
/// for the `JITModule` on translation workers (only the JIT sets
/// `codegen_isa`, the gate for parallel translation), so a JIT-only lowering
/// keyed on the module type must treat it as the JIT too, or worker code
/// diverges from the serial loop (it dropped the vtable receiver guard).
pub(crate) fn is_jit_module<M: ?Sized>() -> bool {
    let name = std::any::type_name::<M>();
    name.contains("JITModule") || name.contains("XlateModule")
}
