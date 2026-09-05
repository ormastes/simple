function tri_and(a,b){ if(a==0||b==0) return 0; if(a==-1||b==-1) return -1; return 1 }
function tri_or(a,b){ if(a==1||b==1) return 1; if(a==-1||b==-1) return -1; return 0 }
function tri_not(a){ if(a==-1) return -1; return (a==1)?0:1 }
function macro_val(m){
  if (m ~ /^(_WIN32|_WIN64|WIN32|__MINGW32__|__MINGW64__|_WINDOWS|SPL_OS_WINDOWS)$/) return 1
  if (m ~ /^(__linux__|__linux|linux|__gnu_linux__|__APPLE__|__MACH__|__unix__|__unix|unix|__FreeBSD__|__NetBSD__|__OpenBSD__|__DragonFly__|__ANDROID__|__EMSCRIPTEN__|__wasm__|__wasm32__|__wasi__|__sun|__HAIKU__|__QNX__|__CYGWIN__|__serenity__)$/) return 0
  if (m ~ /^(_POSIX_VERSION|_POSIX_C_SOURCE|__USE_POSIX|_GNU_SOURCE|__GLIBC__|__BIONIC__|_POSIX_MAPPED_FILES|_POSIX_TIMERS|_POSIX_THREADS|SPL_POSIX)$/) return 0
  if (m ~ /^SPL_BAREMETAL/) return 0
  return -1
}
function ev(s){ pos=1; expr=s; return p_or() }
function skipws(){ while (substr(expr,pos,1)==" "||substr(expr,pos,1)=="\t") pos++ }
function p_or(   l,r){ l=p_and(); while(1){ skipws(); if(substr(expr,pos,2)=="||"){pos+=2; r=p_and(); l=tri_or(l,r)} else return l } }
function p_and(  l,r){ l=p_un();  while(1){ skipws(); if(substr(expr,pos,2)=="&&"){pos+=2; r=p_un();  l=tri_and(l,r)} else return l } }
function p_un(   c,r){ skipws(); c=substr(expr,pos,1)
  if(c=="!"){ pos++; return tri_not(p_un()) }
  if(c=="("){ pos++; r=p_or(); skipws(); if(substr(expr,pos,1)==")") pos++; return r }
  return p_prim() }
function p_prim(  rest,m,v){
  skipws(); rest=substr(expr,pos)
  if (rest=="") { pos++; return -1 }
  if (match(rest,/^defined[ \t]*\([ \t]*[A-Za-z_][A-Za-z0-9_]*[ \t]*\)/)) {
    m=substr(rest,RSTART,RLENGTH); pos+=RLENGTH
    sub(/^defined[ \t]*\([ \t]*/,"",m); sub(/[ \t]*\)$/,"",m); return macro_val(m) }
  if (match(rest,/^defined[ \t]+[A-Za-z_][A-Za-z0-9_]*/)) {
    m=substr(rest,RSTART,RLENGTH); pos+=RLENGTH; sub(/^defined[ \t]+/,"",m); return macro_val(m) }
  if (match(rest,/^[0-9]+/)) { v=substr(rest,RSTART,RLENGTH)+0; pos+=RLENGTH; return (v!=0)?1:0 }
  if (match(rest,/^[A-Za-z_][A-Za-z0-9_]*/)) {
    m=substr(rest,RSTART,RLENGTH); pos+=RLENGTH; skipws()
    if (substr(expr,pos,1) ~ /[<>=+*\/-]/) { while(pos<=length(expr) && substr(expr,pos,2)!="&&" && substr(expr,pos,2)!="||" && substr(expr,pos,1)!=")") pos++; return -1 }
    return macro_val(m) }
  pos++; return -1 }
function curstate(   i,s){ s=1; for(i=1;i<=depth;i++) s=tri_and(s,st[i]); return s }
function curgate(    i,g){ g=""; for(i=1;i<=depth;i++) g=g (g==""?"":" && ") "[" gt[i] "]"; return g }
BEGIN{ depth=0; incomment=0 }
FNR==1{ depth=0; incomment=0 }
{
  line=$0; sub(/\r$/,"",line); raw=line
  if (incomment) { if (match(line,/\*\//)) { line=substr(line,RSTART+RLENGTH); incomment=0 } else next }
  while (match(line,/\/\*/)) { pre=substr(line,1,RSTART-1); post=substr(line,RSTART+2)
    if (match(post,/\*\//)) { line = pre substr(post,RSTART+RLENGTH) } else { line=pre; incomment=1; break } }
  sub(/\/\/.*$/,"",line)
  t=line; sub(/^[ \t]*/,"",t)
  if (substr(t,1,1)=="#") {
    d=substr(t,2); sub(/^[ \t]*/,"",d)
    if (match(d,/^ifdef[ \t]+[A-Za-z_][A-Za-z0-9_]*/)) { e=substr(d,RSTART,RLENGTH); sub(/^ifdef[ \t]+/,"",e); v=macro_val(e); depth++; st[depth]=v; anyT[depth]=v; gt[depth]="ifdef " e; next }
    if (match(d,/^ifndef[ \t]+[A-Za-z_][A-Za-z0-9_]*/)) { e=substr(d,RSTART,RLENGTH); sub(/^ifndef[ \t]+/,"",e); v=tri_not(macro_val(e)); depth++; st[depth]=v; anyT[depth]=v; gt[depth]="ifndef " e; next }
    if (d ~ /^if[ \t(!]/) { e=d; sub(/^if[ \t]*/,"",e); v=ev(e); depth++; st[depth]=v; anyT[depth]=v; gt[depth]="if " e; next }
    if (d ~ /^elif[ \t(!]/) { if(depth>0){ e=d; sub(/^elif[ \t]*/,"",e); v=ev(e); st[depth]=tri_and(v,tri_not(anyT[depth])); anyT[depth]=tri_or(anyT[depth],v); gt[depth]="elif " e } next }
    if (d ~ /^else([ \t]|$)/) { if(depth>0){ st[depth]=tri_not(anyT[depth]); gt[depth]="else-of " gt[depth] } next }
    if (d ~ /^endif([ \t]|$)/) { if(depth>0) depth--; next }
    next
  }
  if (raw ~ /^[A-Za-z_]/ && raw !~ /;[ \t]*$/ && raw !~ /^(extern|typedef)[ \t]/) {
    if (match(line,/(^|[ \t*])rt_[A-Za-z0-9_]+[ \t]*\(/)) {
      sym=substr(line,RSTART,RLENGTH); gsub(/[^A-Za-z0-9_]/,"",sym)
      isstatic = (line ~ /^static[ \t]/) ? 1 : 0
      printf "%s\t%d\t%d\t%s:%d\t%s\n", sym, curstate(), isstatic, FILENAME, FNR, curgate()
    }
  }
}
