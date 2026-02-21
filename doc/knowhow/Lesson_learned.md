# What learned

I was writing 1M lines of code. 
Now it become 400K test code and 100K logic code by keep remove duplication and delete rust impl.
I want to write how I write 1M lines of codes with llm(mostly claude, often with codex)

## remove duplications
often remove duplication add code to code base.
llm often make duplicated codes which make breaking code.
llm update only one duplication of code and add features to the logic.
and add other logics to another duplication.
it will be not able to merge when this two feature go too long.
I personal prefer 5 lines or more duplications.
In addtion to it,
1. do cosign duplication check, but it takes too long time to check.
2. do sementic duplication check and remove by llm or by tool.
3. manual check, folder and files. (It should be done, specially when you did archtectural refactoring, llm often not delete or recover it from history) 
4. arch or file change should throughly updated.
5. do remove duplication on doc too. it is easily overlook and I often overlook overtime which make problems.

and do not make module which do similar works. if needed separate it for other place or design to not use it.
when branch/workspace done, imediatedly merge or rebase then continue again.

## make files less then 1000lines
do not make file large files on md and src.
My personal favorite is 800 lines. 
when lines are too long often it cause llm to read too much.
when it read too much, it become dum.
Some files can not be smaller than 1000 lines manually review it is not separated.

these two are most important.
with this rule. can make 1M lines.

## use best model
use best model like opus for most job.
least do opusplan mode.
less intelligent model often make duplication on src code and make dummy or mock codes.

## use different model to verify
Codex less efficiently write long code but can verify duplication and dummy implementation better.
when make very big logic writing verify it with different model.
A month ago codex and now is diffferent now. especially for biggest model. It use tools properly but still do thing not efficiently like claude.
Not only verify often some model can not solve problem often other big model can solve. if your model on stuck on impl some feature, try to use other big models.


## Do not dirty your startup context
Start up part is not equal to other text. 
often llm more do attension like human does or more.

### do not install much mcp
install mcp as small as possible unless you have some specific reason.
often it is enough just install the language mcp only.
llm company made llm can do anything without other tools.
and install llm company suggested mcp version rather most famous MCP on that langauge or secion.
official mcp already trained for the llm and will not fotget or miss use how to use mcp.
Mcp it self make context longer especially for important startup contexts.
enable other mcp only on agents as private.

### short claude.md or agents.md short as possible.
add on skill or agent in detail
add key to search skill and agent.
and often made mistakes.

## Do more system test but less mock test.
each feature should checked with system test with e2e.
do make script or lib to check system test not to use mock or stub.
 > it is one reason I made langauge to prevent it.
do not allow system test to use mock.
when make failure system test need mock try to use container/vm.
or, make whole separate code base which separate from other system test and allow mock.
you can add integration/unit tests as you wish.
Do actual your manual test for each group of features.
Do check with other language model about dummy impl.

## reduce public interface as much as possible
__init__ or some lanugae dir package export feature should used and limit public interface.
do not use * for export to prevent brainless export.
 > I made language to handle this. folder base public handle with feature group base friend public to support.
when it need to see much it become dum exponentially.
it is reason least you install mcp for main language even though startup part of context is precious.


## use similar environment as llm trained as.
it do much better development when it is unix like environments.
fill much dum without explicite check. it is obiously dum on windows.
list install mingw or linux like tools to mimic linux if you need windows.

and as discribed previously if llm provide some mcp which other public mcp has more user.
it is much better to use provided by llm company unless it is too buggy which is unlikely.

use git yes, I use jj if you see the repository you can findout.
I like jj and want to be familar to jj but it is much better to use git.

## Use strongly type language which compiled fill like it will run.
rust, java, erlang are familar with if compile run as meent to be.
(I don't tried erlan though, does any one try to erlang? llm may not produce erlang properly since it is not popular language as much as rust or java)
I tried typescript but does not have good experience but it may be because few month earlyer experience.
Just few month a go llm had problem with create over 1000 lines of codes but now produce 10k 100k code easily.
Language meant to be strong type and robust implementation target makes llm easily write long codes.
 > rust is good language when try to make may own lanaguage but it become more like rust than I expected.
 > rust's good part but I hate is its borrowing is too difficult to beginner. So, I limit borrowing only for limited situation to be simple.

## keep eyes on it.
see what it does during it works with multiple pane.
let it suggest production examples when do my request. request result format might very differnt by cases.
First verify that llm try to build result is what you wanted and it will show you llm's complete misunder standing.
which you didn't notices and changes go on. it is very hard to find and fix.
complete misunderstanding happen because your sentence become more short and shorter by time, it is inevitable. 
least you check what llm try to makes. check buliding logic's example output check may helpful.

## do research
do research to learn llm to impl this similar feature, outside world what did.
what problem often happen in the domain and solutions. what is common way to impl.
and what code/design on current code base related.
then do arch/design and update doc
then plan

## BDD(TDD)
impl with system test must involve tdd.
bdd is better because it can be feature doc also.


## TLDL
minimum mcp, claude.md
remove duplications
make contents short.
keep eyes on it.
do research about problem and current impl.
use strong type language (most cases just rust/java?)which feel like writing code with compile pass can just works.
