{-
  This module contains all the functions related to the "big/step semantics" of the language.
-}

module Evaluation where
  open import Syntax

  {-
    The function "eval" evaluates the term from the syntax in an final term,
    which is the result of the evaluation.
  -}
  eval : Exp T → T
  eval (val x)      = x
  eval (add e₁ e₂)  = eval e₁ + eval e₂
  eval (min e₁ e₂)  = eval e₁ - eval e₂ 
  eval (mul e₁ e₂)  = eval e₁ * eval e₂
  eval (if b e₁ e₂) with (eval b)
  ... | false = eval e₂
  ... | true  = eval e₁
