{-
  This module contains the representation of a stack-machine in which are execute operations.
  The idea is to "translate" the evaluation's terms in operations for the stack-machine.
-}

module Compiler where
  open import Agda.Builtin.List
  open import Syntax

  {-
    As before, the decision to use variables to express stacks is for
    not to represent every time the type.
  -}
  variable
    S S' S'' : List Set

  {-
    The Stack contains terms that will be used by
    the operations of the stack-machine.
  -}
  data Stack : List Set → Set where
    ∅   : Stack []
    _▷_ : T → Stack S → Stack (T ∷ S)

  {-
    Since the Code term maps List Set, there is the need to operate in an bigger
    universe, so it's used the Set₁ universe.
  -}
  data Code : List Set → List Set → Set₁ where
    PUSH  : T → Code S (T ∷ S)
    _+++_ : Code S S' → Code S' S'' → Code S S''
    ADD   : Code (Nat ∷ Nat ∷ S) (Nat ∷ S)
    MIN   : Code (Nat ∷ Nat ∷ S) (Nat ∷ S)
    MUL   : Code (Nat ∷ Nat ∷ S) (Nat ∷ S)
    IF    : Code S S' → Code S S' → Code (Bool ∷ S) S'

  {-
    The "compile" function translates from the arithmetic expression
    language to operations for the stack-machine.
  -}
  compile : Exp T → Code S (T ∷ S)
  compile (val x)      = PUSH x
  compile (add e e₁)   = (compile e +++ compile e₁) +++ ADD
  compile (min e e₁)   = (compile e +++ compile e₁) +++ MIN
  compile (mul e e₁)   = (compile e +++ compile e₁) +++ MUL
  compile (if b e e₁)  = compile b +++ IF (compile e) (compile e₁)

  {-
    The "exec" function executes all the operations inside a stack,
    and return a nwe stack in which there is the final term.
  -}
  exec : Code S S' → Stack S → Stack S'
  exec (PUSH x) s         = x ▷ s
  exec (c +++ c₁) s       = exec c₁ (exec c s)
  exec ADD (x ▷ (y ▷ s)) = (y + x) ▷ s
  exec MIN (x ▷ (y ▷ s)) = (y - x) ▷ s
  exec MUL (x ▷ (y ▷ s)) = (y * x) ▷ s
  exec (IF c c₁) (b ▷ s) with b
  ... | false = exec c₁ s
  ... | true  = exec c s
