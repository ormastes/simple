# How I write million lines of code with llmß

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
for claude.md, do make 200 lines or less move to skills or something.

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

## addition tool suggest
there is very good tools like centext-mode it seems reduce token well.
do not install lsp mcp but use plugin it consume less token and claude familiar with it.
do not install mcp as possible as. 


## keep quality numbers
keep duplicateion small
keep file size small
keep cohesion size small
keep public interface small
keep coverage big


## start part until overall basic structure sattle.
very hard system test and high coverage during startup and whole structure complete.
do simple implementation and much as possible until basic strcuture sattle.
do make anchor points which pass almost all tests. separate long run tests and normal short run tests.


# Claude Code에 수백 달러 태우고 얻은 교훈 (내돈내산)

Claude Code를 수개월간 실무에 투입하면서, 꽤 비싼 수업료를 내고 체득한 것들을 정리한다. 공식 문서 어디에도 없는, 돈으로 산 실전 노하우다.

---

## 1. Context는 적이다 — `/clear`와 `/compact`를 습관화하라

대화가 길어질수록 LLM의 성능은 **기하급수적으로** 떨어진다. 선형이 아니다. 어느 시점을 넘으면 눈에 띄게 멍청해진다.

작업 단위마다 `/clear`로 세션을 리셋하는 것이 이상적이고, 최소한 `/compact`로 기존 맥락을 요약해 context를 정리해야 한다. "귀찮으니까 이어서 하자"는 마음이 가장 비싼 실수를 만든다.

## 2. 모델은 Opus를 써라, 최소한 `opusplan`을 써라

큰 작업에서 발생하는 황당한 실수 — 존재하지 않는 API를 호출한다거나, 방금 고친 버그를 다시 만든다거나 — 의 대부분은 Sonnet 같은 작은 모델에서 발생한다. Opus도 물론 실수하지만, 빈도와 심각도가 다른 차원이다.

비용이 부담되면 `opusplan` 모델을 쓰라. Plan은 Opus로, 실행은 Sonnet으로 처리하는 모드인데, 순수 Sonnet 대비 결과물의 품질 차이가 크다. 계획 수립의 품질이 실행 전체를 좌우하기 때문이다.

## 3. `claude.md`는 적을수록 좋다

이게 가장 반직관적인 교훈이었다. `claude.md`에 규칙을 장황하게 적으면 성능이 **오히려 떨어진다**. Claude가 마음에 안 들면 어차피 안 지킨다. 지키지도 않을 규칙이 초반 context만 잡아먹는 셈이다.

**넣어야 할 것:**
- 프로젝트 고유의 폴더 구조 (일반적인 구조라면 이마저도 불필요)
- Claude가 **반복적으로** 저지르는 특정 실수를 방지하는 구문
- 전반적인 기반 지식 (예: "C++ 기반 베어메탈 환경", "BDD 개발 방식")

**넣지 말아야 할 것:**
- 상식적인 코딩 규칙
- 일반적인 코드 스타일 가이드
- Claude에게 "이렇게 행동해라" 식의 행동 강령

복잡한 지침이 필요하다면 skill이나 agent에 분리하는 것을 고려하라. `claude.md`를 아예 작성하지 않는 것이 Claude로 대충 생성한 `claude.md`를 쓰는 것보다 눈에 띄게 성능이 좋다.

## 4. MCP는 하나만 — 초반 Context는 금이다

해당 개발 언어의 MCP 하나 정도만 설치한다. 3번과 같은 이유다. MCP를 설치할수록 초반 context에 도구 스키마가 쌓이고, 그만큼 본 작업에 쓸 인지 자원이 줄어든다.

정말 필요한 추가 MCP가 있다면, 메인 세션이 아닌 sub-agent에 설치하는 것을 고려하라.

## 5. Unix 기반 환경을 써라

사람도 낯선 환경에서 작업 능률이 떨어지듯, Claude도 마찬가지다. 학습 데이터의 대부분이 Unix/Linux 기반이기 때문에, 어려운 작업일수록 Windows 환경에서의 성능 저하가 두드러진다.

Windows에서 작업해야 한다면 최소한 MSYS2나 Git Bash 같은 Unix 호환 셸을 사용하라.

## 6. 언어 MCP의 LSP가 정상 작동하는지 확인하라

언어 MCP 설치 여부는 코드베이스가 커질수록 LLM 성능에 결정적인 차이를 만든다. 대부분의 언어 MCP는 내부적으로 LSP(Language Server Protocol)를 통해 코드를 분석하며, 일부는 DAP(Debug Adapter Protocol)로 디버깅까지 지원한다.

핵심은 **LSP가 정상 작동해야 한다**는 것이다. 예를 들어, C++에서 헤더 파일의 의존성이 꼬여 있거나 과도한 include로 LSP가 제대로 동작하지 않으면, 언어 MCP도 무용지물이 되고 LLM은 최적의 성능을 발휘할 수 없다.

## 7. 큰 프로젝트에는 강타입 언어를 선택하라

수만 라인 규모의 프로젝트에서 Claude의 진가는 Rust나 Java 같은 강타입(strongly-typed) 언어에서 발휘된다. 컴파일러가 잡아주는 안전망이 있으면 LLM이 생성한 코드의 결함이 즉시 드러나고, 빠르게 수정된다.

동적 타입 언어에서는 코드가 커질수록 Claude가 만든 버그가 런타임까지 숨어들어 디버깅 비용이 기하급수적으로 늘어난다.

## 8. 작업 전에 Research 문서를 먼저 만들게 하라

바로 구현에 들어가지 말고, 해당 작업에 필요한 외부 자료 조사와 현재 코드베이스 분석을 문서로 먼저 정리하게 하라. 이 한 단계가 결과물의 품질을 극적으로 끌어올린다.

"X를 구현해줘"보다 "X를 구현하기 위해 필요한 리서치 문서를 먼저 작성해줘. 관련 외부 자료와 현재 코드베이스의 관련 부분을 정리해줘"가 훨씬 좋은 코드를 만든다.

## 9. Plan 단계에서 예상 결과물의 선택지를 요청하라

Plan을 세울 때 "예상되는 결과물의 방향을 2~3가지로 보여달라"고 하라. 그래야 Claude가 임의로 선택한, 내 취향과 동떨어진 결과물을 받아든 뒤 처음부터 다시 하는 낭비를 피할 수 있다.

내가 원하는 방향을 사전에 확정하는 것이 context와 비용 모두를 아끼는 길이다.

## 10. Multi-Agent를 적극 활용하라

단일 에이전트로 모든 것을 처리하려 하지 마라. Multi-agent 또는 agent team 구성은 같은 작업에서 눈에 띄게 좋은 결과를 가져온다.

개인적인 체감으로는 agent team 방식이 단순 multi-agent보다 약간 더 안정적인 결과를 내는 느낌이다 (다만 이 기능이 안정화된 지 얼마 되지 않아 아직 더 지켜볼 필요가 있다).

---

## 마치며

결국 관통하는 원칙은 하나다: **Claude의 context를 소중히 다뤄라.** `claude.md`를 짧게 유지하고, MCP를 최소화하고, `/clear`를 습관화하는 것은 모두 같은 맥락이다. LLM에게 context window는 곧 작업 기억(working memory)이고, 이 한정된 자원을 본 작업에 최대한 집중시키는 것이 비용 대비 최고의 결과를 얻는 핵심이다.