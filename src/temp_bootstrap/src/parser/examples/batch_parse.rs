use simple_parser::Parser;
use std::env;
use std::fs;
use std::path::Path;

fn parse_file(path: &Path) -> Result<(), String> {
    let source = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let mut parser = Parser::new(&source);
    parser.parse().map_err(|e| format!("{:?}", e))?;
    Ok(())
}

fn main() {
    let mut pass = 0usize;
    let mut fail = 0usize;
    let mut errors: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
    let mut failed_files = Vec::new();

    for arg in env::args().skip(1) {
        let path = Path::new(&arg);
        match parse_file(path) {
            Ok(()) => pass += 1,
            Err(e) => {
                fail += 1;
                failed_files.push((arg, e.clone()));
                // Extract the error kind
                let key = if let Some(idx) = e.find('{') {
                    if let Some(exp) = e.find("expected:") {
                        let rest = &e[exp..];
                        if let Some(found_idx) = rest.find("found:") {
                            let expected = rest[10..found_idx].trim().trim_matches('"').trim_matches(',');
                            let after_found = &rest[found_idx+7..];
                            let found = if let Some(q1) = after_found.find('"') {
                                let after_q = &after_found[q1+1..];
                                if let Some(q2) = after_q.find('"') {
                                    &after_q[..q2]
                                } else { "?" }
                            } else { "?" };
                            format!("expected {}, found {}", expected, found)
                        } else { e[..std::cmp::min(80, e.len())].to_string() }
                    } else { e[..std::cmp::min(80, e.len())].to_string() }
                } else { e[..std::cmp::min(80, e.len())].to_string() };
                *errors.entry(key).or_insert(0) += 1;
            }
        }
    }

    println!("TOTAL: {}  PASS: {}  FAIL: {}", pass + fail, pass, fail);

    if !errors.is_empty() {
        let mut sorted: Vec<_> = errors.into_iter().collect();
        sorted.sort_by(|a, b| b.1.cmp(&a.1));
        println!("\nError categories:");
        for (err, count) in &sorted {
            println!("  [{:3}] {}", count, err);
        }
    }

    if env::var("SHOW_FAILURES").is_ok() && !failed_files.is_empty() {
        println!("\nFailed files:");
        for (f, e) in &failed_files {
            println!("  {} -> {}", f, &e[..std::cmp::min(120, e.len())]);
        }
    }
}
