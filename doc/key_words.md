# Key words and key points

## Linker Wrapper
It read smf file and call native linker to link file.
In most case, mold is used as native linker if possible.
Smf Getting happen by SmfGetter.
It return obj buffer and linker wrapper send it to native linker.

## Smf Getter 
It read requested smf file and return obj buffer.
However template class or type inference deffered obj are may not generated yet.
In that case, Smf Geteter will compile and generate obj buffer and return obj buffer.
Right after return obj buffer, Smf Getter will update smf file with new generated obj buffer.
Smd Getter may request maximum expected memory for obj buffer to allocator and return only remains after obj buffer is placed.

## Smf Loader
It load obj through smf getter.
Mapping obj buffer to memory with obj mapper.
It may need to update obj buffer especially when obj is not PIC built or some other reason.
When it get location and size of obj buffer. it transform obj buffer if needed.
However, currently, Obj is compiled only with PIC, so may not needed to transform obj buffer.
It will place on execution memory by call memory copyer. and most case will do nothing.
It will share many logic with remote interpreter.

## Obj mapper
It manage symbol location and symbol size of obj buffer.
It maintain symbol table.
It do alloc space for new object.
It do defregments obj buffer with memory copyer
It do calc fregmentation rate.
In real implementation, to load obj buffer, smf loader send obj mapper as memory allocator to Smf getter. To minimize, memcpy

## Remote interpreter
It run program in remote device.
It generate jit code Obj mapper manage jit codes and symbols.
Take memory jit to place let ask maximum jit code size expected to obj mapper and return remain memory after placed.
let memory copyer to place jit code to memory. in this case, remote device.
but for local interpreter actually do nothing.
Local interpeter is actually same except memory copyer

## Remote Smf Loader
Not yet available. 
However with Remote interpreter. it will easy impl.

## Memory copyer
It copy memory from source to destination. 
In most location case, it do nothing.
For remote basemetal, it coy memory from host to remote device by gdb or trace32 debugger.

## Switchable backend
Simple has 2 backends. LLVM and Cranlift.
LLVM for release and native build.
Cranlift for debugging and development and smf. 
when it is release build smf is built with LLVM and it should tagged with compile options to distinguish Cranlift obj in smf.
when release build Linker Wrapper request smf Getter to llvm gen obj buffer. So, during release build smf should compiled with LLVM rather default Cranlift.

## Fully shared frontend
Lexer, Treesitter, Parser. should share code without duplication.
Lexer used by Treesitter and Treesitter used by parser in layered arch.
Interpreter, Loader, compiler use same frontend.
Common logic should applied to frontend or right after it to avoid code duplication.
Intereter, loaader, compiler will be distinguished by configure.


## Boostrap
Bootstrap made by 5 step. 
1. seed: which is written in C++ and can compile Seed Simple Grammar with clang/LLVM.
It impled with C++20 Clang-20.
2. core: Pure simple implementation of simple. It can compile core grammar simple code.
  2-1. core1: it is compiled by seed.
  2-2. core2: it is compiled by core1
It impled with seed simple grammar.
3. full: It is simple with all feature. It can compile full grammar simple code.
  3-1. full1: it is compiler by core2
  3-2. full2: it is compiled by full1
It impled with core simple grammar.
Development is cmake/ninja based.

## Deployment Coverage check
"@deplyment_coverage" is tagged testcase.
It run 2 times.
1. all selected deployment coverage testcases are run first.
when it run callback coverage verifier to runner.
actually it is logged as deployment coverage test loading step.
2. when all none deployment coverage test are ran, it run callback coverage verifier.
it will be showed deployment coverage test running step.
will result by coverage verifier.
Test runner to check file coverage which deployment coverage testcase monitoring to gen coverage on different directories.
before to go 2. step, make link files to overall coverage directory and make each depoyment coverage tests directoy and make link on there.
It can specify coverage listen target by file(however it not specify filename self but module path), and threashold by file or class.

