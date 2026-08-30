fn main() {
    let path = std::env::args().nth(1).expect("fixture path");
    let metadata = std::fs::metadata(path).expect("fixture metadata");
    let mtime = metadata
        .modified()
        .expect("modified time")
        .duration_since(std::time::UNIX_EPOCH)
        .expect("mtime after Unix epoch")
        .as_secs();
    println!("{mtime}");
}
