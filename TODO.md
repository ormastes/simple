# Todo

## dirctory __init__.spl

## compile type inference
manage user refrrences
whenever user changes instanciate class, function.
ex, user call func with int arg instanciate func with int arg type.

## smf loading improvment
just loadin and make runnable smf
link smf 
manage referneces (this can be shared logic with build reference management)
smf swap with new smf
migrate smf to setttlement place(which form like a executable)
make one settlement as executable
remove smf from settlement
embed startup code to start settlment smf 
ref class loader in java
some vm dynamic replacement
see erlang hot code replacement


## packaging
modified zip package.
header file on tail.
let exe at front od zip with out compression.
lest files zipped after exe.
then there not compressed config files. (package, lock)


exe no compressed
zipped all other files
lock no compressed
config no compressed
zip header

so, let it executable as is.

## gpu (cuda) support
 how efficiently express gpu operatioms.
share same operations between threads
less effificent branch
bank separation

## embedded support
startup code for embedded system
teardown bin from settlement smf
float less
os alloc less
thread less
gs less
