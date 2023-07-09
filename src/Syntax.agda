{-
  This module contians the Abstract Syntax Tree of the language.
-}

module Syntax where
  open import Agda.Builtin.Nat  public
  open import Agda.Builtin.Bool public

  {-
    Auxiliar function for show the correctness of the "if" constructor.
    Since it's more difficult to use functions that use the "with" constructor inside 
    the equational reasoning, this "if" representation can be used easli inside that proof.
  -}
  if_then_else_ : {A : Set} → Bool → A → A → A
  if false then a else c = c
  if true  then a else c = a

  {-
    Using a variable in order to not replicate over and over
    the type-signature of T.
  -}
  variable
    T : Set

  {-
    The expression are based on the index type T, obtaining
    an type-safe language representation.
  -}
  data Exp : Set → Set where
    val : T → Exp T
    add min mul : Exp Nat → Exp Nat → Exp Nat
    if : Exp Bool → Exp T → Exp T → Exp T
