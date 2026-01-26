" Simple Language Brief View - Vim Plugin
" Provides semantic folding for Simple language files to show collapsed code overview
"
" Installation:
"   1. Copy this file to ~/.vim/plugin/simple_brief_view.vim
"   2. Or add to your Vim config: source /path/to/brief_view.vim
"
" Usage:
"   :SimpleBrief      - Collapse all, show only signatures
"   :SimpleBriefAll   - Expand all folds
"   :SimpleBriefToggle - Toggle current fold
"
" The plugin uses tree-sitter folds.scm for semantic folding when available,
" falling back to expression-based folding for compatibility.

if exists('g:loaded_simple_brief_view')
    finish
endif
let g:loaded_simple_brief_view = 1

" Save cpo
let s:save_cpo = &cpo
set cpo&vim

" Brief view - collapse all to show only signatures
function! SimpleBriefView()
    " Set fold method to use our expression
    setlocal foldmethod=expr
    setlocal foldexpr=SimpleFoldExpr(v:lnum)
    setlocal foldlevel=0
    setlocal foldminlines=1

    " Fold all - show only signatures
    normal! zM

    echo "Simple Brief View: showing signatures only. Use :SimpleBriefAll to expand."
endfunction

" Expand all folds
function! SimpleBriefAllView()
    normal! zR
    echo "Simple Brief View: all code expanded."
endfunction

" Toggle current fold
function! SimpleBriefToggle()
    normal! za
endfunction

" Fold expression function
" Returns fold level for each line:
"   >1 = start a fold at level 1
"   =  = same level as previous line
"   1  = fold level 1
"   <1 = end a fold at level 1
"   0  = no fold
function! SimpleFoldExpr(lnum)
    let line = getline(a:lnum)
    let trimmed = substitute(line, '^\s*', '', '')

    " Skip empty lines
    if trimmed == ''
        return '='
    endif

    " Skip comments
    if trimmed =~ '^#'
        return '='
    endif

    " Function definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?\(async\s\+\)\?fn\s\+\w\+'
        return '>1'
    endif

    " Static function definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?static\s\+fn\s\+\w\+'
        return '>1'
    endif

    " Mutable method definitions (me) start a fold
    if trimmed =~ '^\(pub\s\+\)\?me\s\+\w\+'
        return '>1'
    endif

    " Class definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?class\s\+\w\+'
        return '>1'
    endif

    " Struct definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?struct\s\+\w\+'
        return '>1'
    endif

    " Enum definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?enum\s\+\w\+'
        return '>1'
    endif

    " Trait definitions start a fold
    if trimmed =~ '^\(pub\s\+\)\?trait\s\+\w\+'
        return '>1'
    endif

    " Impl blocks start a fold
    if trimmed =~ '^impl\s\+\w\+'
        return '>1'
    endif

    " describe/context/it blocks for tests start a fold
    if trimmed =~ '^\(describe\|context\|it\)\s\+'
        return '>1'
    endif

    " Check if we're inside a definition by looking at indentation
    let indent = indent(a:lnum)
    let prev_indent = a:lnum > 1 ? indent(a:lnum - 1) : 0

    " If indentation decreases significantly, might be end of block
    if indent < prev_indent && prev_indent > 0
        return '<1'
    endif

    " Default: same fold level
    return '='
endfunction

" Custom fold text for cleaner display
function! SimpleFoldText()
    let line = getline(v:foldstart)
    let trimmed = substitute(line, '^\s*', '', '')

    " Remove trailing colon if present
    let trimmed = substitute(trimmed, ':\s*$', '', '')

    " Count lines in fold
    let fold_size = v:foldend - v:foldstart + 1

    " Get indentation
    let indent = repeat(' ', indent(v:foldstart))

    " Build fold text
    return indent . trimmed . ' ... (' . fold_size . ' lines)'
endfunction

" Set fold text function for Simple files
augroup SimpleBriefViewFoldText
    autocmd!
    autocmd FileType simple setlocal foldtext=SimpleFoldText()
augroup END

" Commands
command! SimpleBrief call SimpleBriefView()
command! SimpleBriefAll call SimpleBriefAllView()
command! SimpleBriefToggle call SimpleBriefToggle()

" Mappings (optional, uncomment to enable)
" nnoremap <leader>sb :SimpleBrief<CR>
" nnoremap <leader>sa :SimpleBriefAll<CR>
" nnoremap <leader>st :SimpleBriefToggle<CR>

" Auto-apply brief view for Simple files (optional, uncomment to enable)
" augroup SimpleBriefViewAuto
"     autocmd!
"     autocmd FileType simple call SimpleBriefView()
" augroup END

" Restore cpo
let &cpo = s:save_cpo
unlet s:save_cpo
