n=$1; p=$2
cat > tmpdrv/b_run.spl <<EOF
use std.nogc_sync_mut.compression.gzip.lz77.{lz77_compress}
use std.nogc_sync_mut.compression.gzip.deflate.{deflate_block_fixed}

fn mkdata(n: i64) -> [u8]:
    var d: [u8] = []
    var s = 12345
    var i = 0
    loop:
        if i >= n:
            break
        s = (s * 1103515245 + 12345) & 0x7fffffff
        d.push(((s >> 16) & 0xff).to_u8())
        i = i + 1
    return d

fn main():
    val d = mkdata($n)
    val ph = "$p"
    if ph == "mkonly":
        print("d=" + d.len().to_string())
        return
    val toks = lz77_compress(d, 6)
    if ph == "lz77":
        print("toks=" + toks.len().to_string())
        return
    val blk = deflate_block_fixed(toks, true)
    print("out=" + blk.len().to_string())
EOF
