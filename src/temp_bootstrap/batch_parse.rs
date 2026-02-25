// Quick batch parse test - compile with:
// rustc --edition 2021 -L target/debug/deps --extern simple_parser=target/debug/libsimple_parser-*.rlib batch_parse.rs
// Or just run via cargo test

use std::path::Path;

fn parse_file(path: &Path) -> Result<(), String> {
    let content = std::fs::read_to_string(path)
        .map_err(|e| format!("read error: {}", e))?;
    let mut parser = simple_parser::Parser::new(&content);
    parser.parse().map_err(|e| format!("{}", e))?;
    Ok(())
}

fn main() {
    let src_dir = std::env::args().nth(1).unwrap_or_else(|| "../../src/compiler".to_string());
    let mut ok = 0;
    let mut fail = 0;
    let mut errors: Vec<(String, String)> = Vec::new();

    for entry in walkdir::WalkDir::new(&src_dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().map_or(false, |ext| ext == "spl"))
    {
        let path = entry.path();
        match parse_file(path) {
            Ok(_) => ok += 1,
            Err(e) => {
                fail += 1;
                errors.push((path.display().to_string(), e));
            }
        }
    }

    let total = ok + fail;
    println!("Parsed: {}/{} ({}%)", ok, total, if total > 0 { ok * 100 / total } else { 0 });
    println!("Failed: {}", fail);
    println!();

    // Count error types
    let mut error_counts: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    for (_, e) in &errors {
        // Extract error pattern
        let pattern = if let Some(idx) = e.find(" at ") {
            &e[..idx]
        } else {
            e.as_str()
        };
        *error_counts.entry(pattern.to_string()).or_default() += 1;
    }

    let mut sorted: Vec<_> = error_counts.into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1));

    println!("Error categories:");
    for (pattern, count) in sorted.iter().take(40) {
        println!("  {:3} x {}", count, pattern);
    }
}
