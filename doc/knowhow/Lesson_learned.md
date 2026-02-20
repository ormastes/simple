# What learned

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

## make files less then 1000lines
do not make file large files on md and src.
My personal favorite is 800 lines. 
when lines are too long often it cause llm to read too much.
when it read too much, it become dum.
Some files can not be smaller than 1000 lines manually review it is not separated.

these two are most important.
with this rule. can make 1M lines.





