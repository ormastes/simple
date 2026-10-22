//! In-process `--gc-sections` liveness projection over ELF relocatable objects.
//!
//! The Stage 4 link needs the set of symbols that are still undefined once
//! everything unreachable from the entry points has been discarded: those are
//! the runtime entry points the hosted providers must own. That used to be
//! computed with `cc -nostdlib -Wl,-r -Wl,--gc-sections`, which is only
//! correct under LLD. mold (2.42) and GNU ld.bfd both accept the flags and
//! silently skip the collection under `-r`, so on a host whose default `ld` is
//! mold the projection doubled (775 -> 1564 runtime requests on the Phase 4
//! full CLI) and the link failed with "no archive owner" for dead references.
//! See doc/08_tracking/bug/stage4_live_projection_mold_ignores_gc_sections_2026-10-20.md.
//!
//! This pass reproduces LLD's section-granular mark phase directly over the
//! object symbol/relocation graph, so the result no longer depends on which
//! linker the host provides:
//!
//! * roots: the sections defining the requested root symbols, plus sections
//!   LLD always retains (init/fini arrays, ctors/dtors, `.init`/`.fini`,
//!   SHT_NOTE, SHF_GNU_RETAIN);
//! * a live section makes live every section its relocations reach, through
//!   local/section symbols in the same object or through the global symbol
//!   table (strong definition wins over weak, first COMDAT group wins);
//! * SHF_LINK_ORDER sections follow their parent;
//! * `.eh_frame` and non-SHF_ALLOC sections never make anything live;
//! * `__start_X`/`__stop_X` references keep the sections named `X`.
//!
//! The result is every global symbol that a live section references (or a
//! root names) and that no object defines. Any object that cannot be parsed
//! as ELF64 is an error: there is no fallback to a linker invocation.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use object::elf;
use object::read::elf::{ElfFile64, FileHeader, SectionHeader};
use object::{Endianness, Object, ObjectComdat, ObjectSection, ObjectSymbol, RelocationTarget, SymbolSection};

const SHF_GNU_RETAIN: u64 = 0x0020_0000;

#[derive(Clone, Copy)]
enum Edge {
    Local(usize),
    Global(u32),
}

struct SectionNode {
    name: String,
    /// Sections LLD never collects.
    retained: bool,
    /// Live sections of this kind keep nothing else alive.
    inert: bool,
    /// SHF_LINK_ORDER parent section index.
    link_order_parent: Option<usize>,
    edges: Vec<Edge>,
}

struct ObjectNode {
    /// Indexed by ELF section index; `None` for sections outside the graph
    /// (non-ALLOC, relocation/symbol tables, discarded COMDAT members).
    sections: Vec<Option<SectionNode>>,
    link_order_children: HashMap<usize, Vec<usize>>,
}

#[derive(Clone, Copy)]
enum Definition {
    Section {
        obj: usize,
        sec: usize,
        weak: bool,
    },
    /// Absolute or common: defined, but owns no section to mark.
    Sectionless {
        weak: bool,
        common: bool,
    },
}

impl Definition {
    fn is_weak(self) -> bool {
        match self {
            Definition::Section { weak, .. } | Definition::Sectionless { weak, .. } => weak,
        }
    }
}

#[derive(Default)]
struct Graph {
    names: HashMap<String, u32>,
    name_list: Vec<String>,
    definitions: HashMap<u32, Definition>,
    objects: Vec<ObjectNode>,
    comdats_seen: HashSet<String>,
    object_paths: Vec<String>,
}

impl Graph {
    fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.names.get(name) {
            return id;
        }
        let id = self.name_list.len() as u32;
        self.name_list.push(name.to_string());
        self.names.insert(name.to_string(), id);
        id
    }

    fn define(&mut self, id: u32, def: Definition) {
        match self.definitions.get(&id) {
            // A weak definition yields to the first strong one, and a common
            // symbol yields to a real section definition (as in LLD); any
            // other existing definition wins, matching ELF resolution order.
            Some(Definition::Sectionless { common: true, .. })
                if matches!(def, Definition::Section { weak: false, .. }) =>
            {
                self.definitions.insert(id, def);
            }
            Some(existing) if !existing.is_weak() || def.is_weak() => {}
            _ => {
                self.definitions.insert(id, def);
            }
        }
    }

    fn add_object(&mut self, path: &Path, bytes: &[u8]) -> Result<(), String> {
        let file = ElfFile64::<Endianness>::parse(bytes)
            .map_err(|e| format!("live projection: parse ELF64 object {}: {e}", path.display()))?;
        if file.kind() != object::ObjectKind::Relocatable {
            return Err(format!(
                "live projection: {} is not a relocatable object",
                path.display()
            ));
        }
        let endian = file.endian();
        let headers = file
            .elf_header()
            .section_headers(endian, bytes)
            .map_err(|e| format!("live projection: section headers of {}: {e}", path.display()))?;
        let obj_index = self.objects.len();
        self.object_paths.push(path.display().to_string());

        let mut discarded: HashSet<usize> = HashSet::new();
        for comdat in file.comdats() {
            let name = comdat
                .name()
                .map_err(|e| format!("live projection: COMDAT name in {}: {e}", path.display()))?
                .to_string();
            if !self.comdats_seen.insert(name) {
                discarded.extend(comdat.sections().map(|s| s.0));
            }
        }

        let mut sections: Vec<Option<SectionNode>> = (0..headers.len()).map(|_| None).collect();
        for section in file.sections() {
            let index = section.index().0;
            if discarded.contains(&index) {
                continue;
            }
            let header = &headers[index];
            let flags = header.sh_flags(endian) as u64;
            if flags & u64::from(elf::SHF_ALLOC) == 0 {
                continue;
            }
            let sh_type = header.sh_type(endian);
            let name = section
                .name()
                .map_err(|e| format!("live projection: section name in {}: {e}", path.display()))?
                .to_string();
            let retained = flags & SHF_GNU_RETAIN != 0
                || matches!(
                    sh_type,
                    elf::SHT_NOTE | elf::SHT_INIT_ARRAY | elf::SHT_FINI_ARRAY | elf::SHT_PREINIT_ARRAY
                )
                || is_retained_section_name(&name);
            let link_order_parent = (flags & u64::from(elf::SHF_LINK_ORDER) != 0)
                .then(|| header.sh_link(endian) as usize)
                .filter(|&parent| parent != 0);
            sections[index] = Some(SectionNode {
                inert: name == ".eh_frame",
                name,
                retained,
                link_order_parent,
                edges: Vec::new(),
            });
        }

        // Resolve the object's symbols once: globals by interned name, locals
        // (including section symbols) to their defining section.
        let mut symbol_edges: HashMap<usize, Edge> = HashMap::new();
        for symbol in file.symbols() {
            let name = symbol.name().unwrap_or("");
            if symbol.is_global() || symbol.is_weak() {
                if name.is_empty() {
                    continue;
                }
                let id = self.intern(name);
                symbol_edges.insert(symbol.index().0, Edge::Global(id));
                let weak = symbol.is_weak();
                match symbol.section() {
                    SymbolSection::Section(sec) if sections.get(sec.0).map_or(false, Option::is_some) => {
                        self.define(
                            id,
                            Definition::Section {
                                obj: obj_index,
                                sec: sec.0,
                                weak,
                            },
                        );
                    }
                    SymbolSection::Absolute => {
                        self.define(id, Definition::Sectionless { weak, common: false });
                    }
                    SymbolSection::Common => {
                        self.define(id, Definition::Sectionless { weak, common: true });
                    }
                    // Undefined, or defined in a discarded/non-ALLOC section:
                    // contributes no definition.
                    _ => {}
                }
            } else if let SymbolSection::Section(sec) = symbol.section() {
                symbol_edges.insert(symbol.index().0, Edge::Local(sec.0));
            }
        }

        for section in file.sections() {
            let index = section.index().0;
            let Some(node) = sections[index].as_mut() else {
                continue;
            };
            if node.inert {
                continue;
            }
            for (_, relocation) in section.relocations() {
                let edge = match relocation.target() {
                    RelocationTarget::Symbol(sym) => symbol_edges.get(&sym.0).copied(),
                    RelocationTarget::Section(sec) => Some(Edge::Local(sec.0)),
                    _ => None,
                };
                if let Some(edge) = edge {
                    node.edges.push(edge);
                }
            }
        }

        let mut link_order_children: HashMap<usize, Vec<usize>> = HashMap::new();
        for (index, node) in sections.iter().enumerate() {
            if let Some(parent) = node.as_ref().and_then(|n| n.link_order_parent) {
                link_order_children.entry(parent).or_default().push(index);
            }
        }
        self.objects.push(ObjectNode {
            sections,
            link_order_children,
        });
        Ok(())
    }

    fn undefined_live_symbols(&self, roots: &[&str]) -> Vec<String> {
        let mut live: HashSet<(usize, usize)> = HashSet::new();
        let mut referenced: HashSet<u32> = HashSet::new();
        let mut work: Vec<(usize, usize)> = Vec::new();
        let mut sections_by_name: HashMap<&str, Vec<(usize, usize)>> = HashMap::new();

        for (obj, node) in self.objects.iter().enumerate() {
            for (sec, section) in node.sections.iter().enumerate() {
                if let Some(section) = section {
                    sections_by_name
                        .entry(section.name.as_str())
                        .or_default()
                        .push((obj, sec));
                    if section.retained {
                        work.push((obj, sec));
                    }
                }
            }
        }

        let mut pending_globals: Vec<u32> = roots.iter().filter_map(|root| self.names.get(*root).copied()).collect();
        // A root no object mentions stays undefined, exactly like `-u <root>`
        // on a linker command line.
        let mut unmentioned_roots: Vec<String> = roots
            .iter()
            .filter(|root| !self.names.contains_key(**root))
            .map(|root| root.to_string())
            .collect();

        loop {
            while let Some(id) = pending_globals.pop() {
                if !referenced.insert(id) {
                    continue;
                }
                match self.definitions.get(&id) {
                    Some(Definition::Section { obj, sec, .. }) => work.push((*obj, *sec)),
                    Some(Definition::Sectionless { .. }) => {}
                    None => {
                        let name = &self.name_list[id as usize];
                        for prefix in ["__start_", "__stop_"] {
                            if let Some(target) = name.strip_prefix(prefix) {
                                if let Some(list) = sections_by_name.get(target) {
                                    work.extend(list.iter().copied());
                                }
                            }
                        }
                    }
                }
            }
            let Some((obj, sec)) = work.pop() else {
                break;
            };
            let Some(section) = self.objects[obj].sections.get(sec).and_then(Option::as_ref) else {
                continue;
            };
            if !live.insert((obj, sec)) {
                continue;
            }
            if let Some(children) = self.objects[obj].link_order_children.get(&sec) {
                work.extend(children.iter().map(|&child| (obj, child)));
            }
            for edge in &section.edges {
                match *edge {
                    Edge::Local(target) => work.push((obj, target)),
                    Edge::Global(id) => pending_globals.push(id),
                }
            }
        }

        let mut undefined: Vec<String> = referenced
            .into_iter()
            .filter(|id| !self.definitions.contains_key(id))
            .map(|id| self.name_list[id as usize].clone())
            .collect();
        undefined.append(&mut unmentioned_roots);
        undefined.sort();
        undefined.dedup();
        undefined
    }

    /// Debug aid: one shortest (BFS) reference chain per live undefined
    /// global, as `object:section` hops from a root. `-> sym` marks the
    /// global symbol each hop was reached through.
    fn undefined_live_paths(&self, roots: &[&str]) -> Vec<(String, Vec<String>)> {
        use std::collections::VecDeque;
        type Node = (usize, usize);
        let mut parent: HashMap<Node, Option<(Node, Option<u32>)>> = HashMap::new();
        let mut queue: VecDeque<Node> = VecDeque::new();
        let mut first_ref: HashMap<u32, (Node, Option<u32>)> = HashMap::new();
        for (obj, node) in self.objects.iter().enumerate() {
            for (sec, section) in node.sections.iter().enumerate() {
                if section.as_ref().map_or(false, |s| s.retained) {
                    parent.insert((obj, sec), None);
                    queue.push_back((obj, sec));
                }
            }
        }
        for root in roots {
            if let Some(&id) = self.names.get(*root) {
                if let Some(Definition::Section { obj, sec, .. }) = self.definitions.get(&id) {
                    if !parent.contains_key(&(*obj, *sec)) {
                        parent.insert((*obj, *sec), None);
                        queue.push_back((*obj, *sec));
                    }
                }
            }
        }
        while let Some((obj, sec)) = queue.pop_front() {
            let Some(section) = self.objects[obj].sections.get(sec).and_then(Option::as_ref) else {
                continue;
            };
            let from = (obj, sec);
            let mut next: Vec<(Node, Option<u32>)> = Vec::new();
            if let Some(children) = self.objects[obj].link_order_children.get(&sec) {
                next.extend(children.iter().map(|&c| ((obj, c), None)));
            }
            for edge in &section.edges {
                match *edge {
                    Edge::Local(t) => next.push(((obj, t), None)),
                    Edge::Global(id) => match self.definitions.get(&id) {
                        Some(Definition::Section { obj: o, sec: s, .. }) => next.push(((*o, *s), Some(id))),
                        Some(Definition::Sectionless { .. }) => {}
                        None => {
                            first_ref.entry(id).or_insert((from, Some(id)));
                        }
                    },
                }
            }
            for (node, via) in next {
                if self.objects[node.0].sections.get(node.1).and_then(Option::as_ref).is_some()
                    && !parent.contains_key(&node)
                {
                    parent.insert(node, Some((from, via)));
                    queue.push_back(node);
                }
            }
        }
        let label = |n: Node| {
            let section = self.objects[n.0].sections[n.1].as_ref().map_or("?", |s| s.name.as_str());
            let path = &self.object_paths[n.0];
            let file = path.rsplit('/').next().unwrap_or(path);
            format!("{file}:{section}")
        };
        let mut out = Vec::new();
        for (id, (node, _)) in first_ref {
            let mut chain = vec![format!("=> {}", self.name_list[id as usize])];
            let mut cur = node;
            loop {
                chain.push(label(cur));
                match parent.get(&cur) {
                    Some(Some((prev, via))) => {
                        if let Some(v) = via {
                            chain.push(format!("  via {}", self.name_list[*v as usize]));
                        }
                        cur = *prev;
                    }
                    _ => break,
                }
            }
            chain.reverse();
            out.push((self.name_list[id as usize].clone(), chain));
        }
        out.sort();
        out
    }
}

fn is_retained_section_name(name: &str) -> bool {
    let base = |prefix: &str| name == prefix || name.starts_with(&format!("{prefix}."));
    base(".ctors")
        || base(".dtors")
        || base(".init_array")
        || base(".fini_array")
        || base(".preinit_array")
        || name == ".init"
        || name == ".fini"
        || name == ".jcr"
}

/// Global symbols left undefined after garbage-collecting `objects` from
/// `roots`, i.e. what `ld.lld -r --gc-sections -u <root>...` leaves undefined.
pub(super) fn live_undefined_symbols(objects: &[PathBuf], roots: &[&str]) -> Result<Vec<String>, String> {
    let mut graph = Graph::default();
    for path in objects {
        let bytes = std::fs::read(path).map_err(|e| format!("live projection: read {}: {e}", path.display()))?;
        graph.add_object(path, &bytes)?;
    }
    if let Ok(dest) = std::env::var("SIMPLE_LIVE_PROJECTION_PATHS") {
        // Debug: write one shortest reference chain per live undefined global.
        let mut text = String::new();
        for (name, chain) in graph.undefined_live_paths(roots) {
            text.push_str(&format!("### {name}\n"));
            for hop in chain {
                text.push_str(&format!("{hop}\n"));
            }
        }
        std::fs::write(&dest, text).map_err(|e| format!("live projection: write {dest}: {e}"))?;
    }
    Ok(graph.undefined_live_symbols(roots))
}

#[cfg(test)]
mod tests {
    use super::live_undefined_symbols;
    use object::write::{Object, Relocation, StandardSection, Symbol, SymbolSection};
    use object::{
        Architecture, BinaryFormat, Endianness, RelocationEncoding, RelocationFlags, RelocationKind, SymbolFlags,
        SymbolKind, SymbolScope,
    };
    use std::path::PathBuf;

    fn func_section(obj: &mut Object<'static>, name: &str) -> (object::write::SectionId, object::write::SymbolId) {
        let section = obj.add_subsection(StandardSection::Text, name.as_bytes());
        obj.append_section_data(section, &[0u8; 16], 4);
        let symbol = obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size: 16,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(section),
            flags: SymbolFlags::None,
        });
        (section, symbol)
    }

    fn undefined(obj: &mut Object<'static>, name: &str) -> object::write::SymbolId {
        obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: 0,
            size: 0,
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Undefined,
            flags: SymbolFlags::None,
        })
    }

    fn call(obj: &mut Object<'static>, from: object::write::SectionId, to: object::write::SymbolId) {
        obj.add_relocation(
            from,
            Relocation {
                offset: 0,
                symbol: to,
                addend: 0,
                flags: RelocationFlags::Generic {
                    kind: RelocationKind::Absolute,
                    encoding: RelocationEncoding::Generic,
                    size: 64,
                },
            },
        )
        .unwrap();
    }

    fn new_object() -> Object<'static> {
        Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little)
    }

    fn write(dir: &tempfile::TempDir, name: &str, obj: Object<'static>) -> PathBuf {
        let path = dir.path().join(name);
        std::fs::write(&path, obj.write().unwrap()).unwrap();
        path
    }

    #[test]
    fn dead_function_references_are_not_live_requests() {
        let dir = tempfile::tempdir().unwrap();
        let mut a = new_object();
        let (main_sec, _) = func_section(&mut a, "main");
        let (dead_sec, _) = func_section(&mut a, "dead_fn");
        let rt_live = undefined(&mut a, "rt_live");
        let rt_dead = undefined(&mut a, "rt_dead");
        let helper = undefined(&mut a, "helper");
        call(&mut a, main_sec, rt_live);
        call(&mut a, main_sec, helper);
        call(&mut a, dead_sec, rt_dead);

        let mut b = new_object();
        let (helper_sec, _) = func_section(&mut b, "helper");
        let (other_sec, _) = func_section(&mut b, "unreached");
        let rt_from_helper = undefined(&mut b, "rt_from_helper");
        let rt_unreached = undefined(&mut b, "rt_unreached");
        call(&mut b, helper_sec, rt_from_helper);
        call(&mut b, other_sec, rt_unreached);

        let objects = vec![write(&dir, "a.o", a), write(&dir, "b.o", b)];
        let live = live_undefined_symbols(&objects, &["main", "spl_main"]).unwrap();
        assert_eq!(live, vec!["rt_from_helper", "rt_live", "spl_main"]);
    }

    #[test]
    fn retained_init_array_keeps_its_targets_live() {
        let dir = tempfile::tempdir().unwrap();
        let mut a = new_object();
        let (_main_sec, _) = func_section(&mut a, "main");
        let (ctor_sec, ctor) = func_section(&mut a, "ctor_fn");
        let rt_ctor = undefined(&mut a, "rt_ctor");
        call(&mut a, ctor_sec, rt_ctor);
        let init = a.add_section(Vec::new(), b".init_array".to_vec(), object::SectionKind::Data);
        a.section_mut(init).flags = object::SectionFlags::Elf {
            sh_flags: u64::from(object::elf::SHF_ALLOC | object::elf::SHF_WRITE),
        };
        a.append_section_data(init, &[0u8; 8], 8);
        call(&mut a, init, ctor);
        let objects = vec![write(&dir, "a.o", a)];
        let live = live_undefined_symbols(&objects, &["main"]).unwrap();
        assert_eq!(live, vec!["rt_ctor"]);
    }

    #[test]
    fn real_definition_replaces_an_earlier_common_symbol() {
        let dir = tempfile::tempdir().unwrap();
        let mut a = new_object();
        let (main_sec, _) = func_section(&mut a, "main");
        a.add_symbol(Symbol {
            name: b"shared_state".to_vec(),
            value: 8,
            size: 8,
            kind: SymbolKind::Data,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Common,
            flags: SymbolFlags::None,
        });
        let state_ref = a.symbol_id(b"shared_state").unwrap();
        call(&mut a, main_sec, state_ref);

        let mut b = new_object();
        let (state_sec, _) = func_section(&mut b, "shared_state");
        let rt_init = undefined(&mut b, "rt_state_init");
        call(&mut b, state_sec, rt_init);

        let objects = vec![write(&dir, "a.o", a), write(&dir, "b.o", b)];
        let live = live_undefined_symbols(&objects, &["main"]).unwrap();
        assert_eq!(live, vec!["rt_state_init"]);
    }

    #[test]
    fn unparseable_object_fails_closed() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("junk.o");
        std::fs::write(&path, b"not an object").unwrap();
        assert!(live_undefined_symbols(&[path], &["main"]).is_err());
    }

    /// Set-equality against every undefined symbol an LLD
    /// `-r --gc-sections -u main -u spl_main` projection of a real object set
    /// leaves (`nm -u | awk '{print $NF}' | sort -u`). Run with
    /// `SIMPLE_LIVE_PROJECTION_RSP=<objects.rsp> SIMPLE_LIVE_PROJECTION_EXPECTED=<syms.txt>`.
    #[test]
    #[ignore]
    fn matches_lld_projection_of_real_object_set() {
        let rsp = std::env::var("SIMPLE_LIVE_PROJECTION_RSP").expect("SIMPLE_LIVE_PROJECTION_RSP");
        let expected = std::env::var("SIMPLE_LIVE_PROJECTION_EXPECTED").expect("SIMPLE_LIVE_PROJECTION_EXPECTED");
        let objects: Vec<PathBuf> = std::fs::read_to_string(rsp)
            .unwrap()
            .lines()
            .map(|line| PathBuf::from(line.trim().trim_matches('"')))
            .filter(|path| !path.as_os_str().is_empty())
            .collect();
        let start = std::time::Instant::now();
        let live = live_undefined_symbols(&objects, &["main", "spl_main"]).unwrap();
        eprintln!(
            "live projection: {} objects, {} undefined, {:?}",
            objects.len(),
            live.len(),
            start.elapsed()
        );
        let ours: std::collections::BTreeSet<String> = live.into_iter().collect();
        let lld: std::collections::BTreeSet<String> = std::fs::read_to_string(expected)
            .unwrap()
            .lines()
            .map(str::to_string)
            .filter(|s| !s.is_empty())
            .collect();
        let extra: Vec<_> = ours.difference(&lld).collect();
        let missing: Vec<_> = lld.difference(&ours).collect();
        assert!(
            extra.is_empty() && missing.is_empty(),
            "extra={extra:?} missing={missing:?}"
        );
    }
}
