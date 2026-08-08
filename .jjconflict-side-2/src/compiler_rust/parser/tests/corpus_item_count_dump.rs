//! Corpus dump used as an A/B regression harness for parser changes.
//!
//! Prints `<path>\t<ok|err>\t<top_level_item_count>` for every `.spl` file under
//! the repo source roots. Run it on the BEFORE and AFTER trees and diff the two
//! outputs: any line that changes is a behavioural delta of the parser change.
//!
//! Not an assertion test — it is `#[ignore]`d so it never runs in CI; invoke it
//! explicitly with `--ignored --nocapture`.

use simple_parser::Parser;
use std::path::{Path, PathBuf};

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    let mut entries: Vec<_> = rd.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            collect(&p, out);
        } else if p.extension().is_some_and(|e| e == "spl") {
            out.push(p);
        }
    }
}

#[test]
#[ignore = "A/B harness: run explicitly with --ignored --nocapture"]
fn dump_corpus_item_counts() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap();
    let mut files = Vec::new();
    for sub in ["lib", "app", "compiler"] {
        collect(&root.join(sub), &mut files);
    }
    for f in &files {
        let Ok(src) = std::fs::read_to_string(f) else { continue };
        let rel = f.strip_prefix(root).unwrap_or(f).display();
        let mut p = Parser::new(&src);
        match p.parse() {
            Ok(ast) => println!("{}\tok\t{}", rel, ast.items.len()),
            Err(_) => println!("{}\terr\t0", rel),
        }
    }
    eprintln!("files scanned: {}", files.len());
}
