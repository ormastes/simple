# fix accepted directory targets as empty source

Status: SOURCE-FIXED; fresh pure-Simple qualification remains pending.

## Bug

The public fix owners disagreed on empty reads. One treated a directory or
collapsed read failure as an empty source and returned success; another
rejected valid empty regular files. The standalone owner had a third read path.

## Root fix

All three owners now use `fix_read_source`. It returns `Result`, rejects
missing paths and directories explicitly, rejects nonempty files whose read
collapses to empty, and preserves a valid empty file as `Ok("")`. Both public
contracts require directory exit 1, sentinel nonmutation, and empty-file exit 0.

## Known boundary

The current text-read ABI represents both a zero-byte file and some read
failures as empty text. A zero-byte unreadable regular file therefore cannot be
distinguished without a status-bearing runtime read/open API; this fix does not
claim otherwise.

## Remaining qualification

Run both focused owner contracts once through the next fresh pure-Simple Stage
4 CLI. Retained seed execution is source evidence only.
