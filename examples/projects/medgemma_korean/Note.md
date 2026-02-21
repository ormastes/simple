# What todo

* check kor med exam devided in train, test(validation)
* make shared_logic.spl first and do not make duplicated logic. ✅ DONE

## 0. Prepare english medical training data ✅ IMPLEMENTED
* to prevent english train data forgetting.
* already downloaded some datas.
* **Implementation:** `train_phase0.spl` — trains base model on English medical data with LoRA_0, merges into base weights. Uses `shared_logic.spl` for config and utilities. Falls back to synthetic data when real data files not found.

## 1. small medgemma, large medgemma abilities. ✅ IMPLEMENTED
* prepare validation exam in english
* check what is score of small medgemma, large medgemma.
* decide small medgemma can score more than 97% score in validation
 - test english version of med kore exam validation it is over 97%
 - use large if can not pass.
* **Implementation:** `train_phase1.spl` — evaluates baseline accuracy, skips training if >= 97%. Otherwise adds LoRA_1 and trains. `validation.spl` has `validate_accuracy()` and `check_english_retention()`.


## 1.1. if neither small or large can not meet 97%. ✅ IMPLEMENTED
* add lora1
* translate train data to english too.
* train medgemma in eglish with cross entrophy loss.
* **Implementation:** Handled in `train_phase1.spl` — when accuracy < 97%, automatically adds LoRA_1 and trains. Cross-entropy loss available in `shared_logic.spl` (`compute_ce_loss`).

## 2. create embedding. ✅ IMPLEMENTED
* but add two more embedding to it distinguish korean/english.
* let original token to enable korean embedding, others english.
* can only these two embedding trainable?
* **Implementation:** `train_phase3.spl` + `embedding_utils.spl` — KorEngEmbedding with dual weight tables (kor_weight, eng_weight). Mask-based routing: Korean tokens → kor_embedding, English → eng_embedding. RoPE positional encoding via precomputed sin/cos cache. Mean pooling over sequence dimension. Config: `config/phase3.sdn`.

## 3. train korean text while check english text. ✅ IMPLEMENTED
* train korean text for additional 2 embed and lora1 in cross entrophy loss.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english
* **Implementation:** `train_phase4.spl` + `layer_utils.spl` — ExtendedModel wraps TextModel + embeddings + RoPE. LoRA_3 added to layers 1-2. Per-layer CE loss monitoring. English retention checked every epoch (>= 97%). Recovery sub-loop when retention drops. Config: `config/phase4.sdn`.


## 4. train translation korean. ✅ IMPLEMENTED
* add front most layer and back most layer with duplication of front and end. and make these two layer total trainable.
* train korean text(include med kor format knowledge) for additional 2 embed and lora1 in cross entrophy loss.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english
* train korean translation for additional 2 embed and lora1 in cross entrophy loss, front/back layer.
* "each layer" original layer cross entrophy loss with (+ 2 embedded and lora1, front/back layer) in cross entrophy loss in english medical train data.
 - test english version of med kore exam validation it is over 97% if not do "each layer" train for english
* **Implementation:** `train_phase5.spl` — Front/back layers duplicated from L1/L3 via `duplicate_front_back_layers()`. Sub-phase A: Korean text (front→L1+LoRA→L2+LoRA→L3→back). Sub-phase B: Korean→English translation. LoRA_4 merged after training. Config: `config/phase5.sdn`.


## 5. train reasoning. ✅ IMPLEMENTED
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
* **Implementation:** `train_phase6.spl` — 3 sub-phases: A (Korean text), B (translation), C (exam reasoning). Exam loss = CE*0.6 + format_penalty*0.2 + confidence*0.2. LoRA_5 merged after training. Final comprehensive validation. Config: `config/phase6.sdn`.

---

## Infrastructure Added

### Library Level (src/lib/gc_async_mut/torch/)
- **ops.spl** — Pure Simple composed ops: cross-entropy loss tensor, MSE loss tensor, RMSNorm, gradient clipping, accuracy computation, LR schedules
- **optim.spl** — Real SGD with momentum + Adam optimizer from tensor primitives
- **dyn_ffi.spl** — Added 15 new DynLoader wrappers: sum_dim, mean_dim, argmax, argmin, max_dim, gather, slice, nn_linear, nn_embedding, no_grad_begin/end, CUDA memory ops

### Project Level (examples/projects/medgemma_korean/src/)
- **shared_logic.spl** — TrainConfig (phases 0-6), TrainState, batch creation, loss wrappers, GPU reporting, LR scheduling
- **data_loader.spl** — JSONL pre-tokenized data loading with synthetic fallback
- **model.spl** — Added ModelConfig, checkpoint stubs, print_summary
- **validation.spl** — MCQ accuracy (argmax), 97% threshold, English retention check, Korean/exam validation, extended model validation
- **lora_utils.spl** — Added gradient clipping (lora_clip_and_step)
- **embedding_utils.spl** — KorEngEmbedding (dual Korean/English), RoPECache (sin/cos), mask-based token routing, mean pooling
- **layer_utils.spl** — ExtendedModel (base + embeddings + RoPE + front/back), per-layer CE loss, front/back layer duplication
- **train_phase0.spl** — English medical baseline with shared_logic
- **train_phase1.spl** — evaluate → threshold check → conditional LoRA training
- **train_phase2.spl** — Gradient clipping, English retention per epoch
- **train_phase3.spl** — Embedding training (Korean/English + RoPE, no LoRA)
- **train_phase4.spl** — Korean text + LoRA_3 + per-layer CE + English recovery
- **train_phase5.spl** — Korean translation + front/back layers + LoRA_4
- **train_phase6.spl** — Korean medical exam reasoning + weighted loss + LoRA_5
- **run_all.spl** — Full 7-phase pipeline with extended validation
