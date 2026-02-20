# What todo

* check kor med exam devided in train, test(validation)
* make shared_logic.spl first and do not make duplicated logic.

## 0. Prepare english medical training data
* to prevent english train data forgetting.
* already downloaded some datas.

## 1. small medgemma, large medgemma abilities.
* prepare validation exam in english
* check what is score of small medgemma, large medgemma.
* decide small medgemma can score more than 97% score in validation
 - test english version of med kore exam validation it is over 97%
 - use large if can not pass.
 
 
## 1.1. if neither small or large can not meet 97%.
* add lora1
* translate train data to english too.
* train medgemma in eglish with cross entrophy loss.

## 2. create embedding. check old_py.
* but add two more embedding to it distinguish korean/english.
* let original token to enable korean embedding, others english.
* can only these two embedding trainable? 

## 3. train korean text while check english text.
* train korean text for additional 2 embed and lora1 in cross entrophy loss.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english


## 4. train translation korean.
* add front most layer and back most layer with duplication of front and end. and make these two layer total trainable. 
* train korean text(include med kor format knowledge) for additional 2 embed and lora1 in cross entrophy loss.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english
* train korean translation for additional 2 embed and lora1 in cross entrophy loss, front/back layer.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english


## 5. train reasoning.
* train korean text(include med kor format knowledge) for additional 2 embed and lora1 in cross entrophy loss.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english
* train korean translation for additional 2 embed and lora1 in cross entrophy loss, front/back layer.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english.
* train med kor exam, check reasoning format, check one char answer.
 - not just cross entrophy loss. 
 - test with med kor exam validation data.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english.

