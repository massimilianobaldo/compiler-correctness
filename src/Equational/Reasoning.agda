module Equational.Reasoning where
  open import Agda.Builtin.Equality

  cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong f refl = refl

  symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symm refl = refl

  trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans refl q = q

  infix  3 _∎
  infixr 2 _≡⟨_⟩_ _≡⟨⟩_
  infix  1 begin_

  _≡⟨_⟩_ : {A : Set} {y z : A} → (x : A) → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ p ⟩ q = trans p q

  _≡⟨⟩_ : {A : Set} {y : A} → (x : A) → (q : x ≡ y) → x ≡ y
  x ≡⟨⟩ q = q

  _∎ : {A : Set} → (x : A) → x ≡ x
  x ∎ = refl

  begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
  begin p = p
