module Tests where
  open import Agda.Builtin.Equality
  open import Agda.Builtin.List
  open import Equational.Reasoning
  open import Syntax
  open import Evaluation
  open import Compiler

  program = add (val 1) (if (val true) (mul (val 2) (val 2)) (add (val 1) (val 3)))

  test-eval : eval program ≡ 5
  test-eval = refl

  test-compile : compile program ≡ (PUSH 1 +++ (PUSH true +++ IF ((PUSH 2 +++ PUSH 2) +++ MUL) ((PUSH 1 +++ PUSH 3) +++ ADD))) +++ ADD
  test-compile = refl

  test-exec : exec (compile program) ∅ ≡ 5 ▷ ∅
  test-exec = refl

  test-correct : eval program ▷ ∅ ≡ exec (compile program) ∅
  test-correct = refl
