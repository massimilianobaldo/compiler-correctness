module Correctness where
  open import Agda.Builtin.Equality
  open import Equational.Reasoning
  open import Syntax
  open import Evaluation
  open import Compiler

  correct : (e : Exp T) → (s : Stack S) → eval e ▷ s ≡ exec (compile e) s
  -----------
  -- Value --
  -----------
  correct (val x)      s = refl

  ---------------------------
  -- Arithmetic Expression --
  ---------------------------
  correct (add e₁ e₂)   s = begin
    ((eval e₁ + eval e₂) ▷ s) ≡⟨⟩ -- apply definiton of exec for add (←)
    exec ADD (eval e₂ ▷ (eval e₁ ▷ s)) ≡⟨ cong (λ x → exec ADD (eval e₂ ▷ x)) (correct e₁ s) ⟩ -- inductive hypothesis on e₁ and s, with the addition of "exec ADD (eval e₂ ▷ ...)"
    exec ADD (eval e₂ ▷ (exec (compile e₁) s)) ≡⟨ cong (λ y → exec ADD y) (correct e₂ (exec (compile e₁) s)) ⟩ -- inductive hypothesis on e₂ and (exec (compile e₁) s), adding the "exec ADD" part
    exec ADD (exec (compile e₂) (exec (compile e₁) s)) ∎
  
  correct (min e₁ e₂)   s = begin
    ((eval e₁ - eval e₂) ▷ s) ≡⟨⟩ -- same situastion as "add case"
    exec MIN (eval e₂ ▷ (eval e₁ ▷ s)) ≡⟨ cong (λ x → exec MIN (eval e₂ ▷ x)) (correct e₁ s) ⟩
    exec MIN (eval e₂ ▷ (exec (compile e₁) s)) ≡⟨ cong (λ x → exec MIN x) (correct e₂ (exec (compile e₁) s)) ⟩
    exec MIN (exec (compile e₂) (exec (compile e₁) s)) ∎

  correct (mul e₁ e₂)   s = begin
    ((eval e₁ * eval e₂) ▷ s) ≡⟨⟩ -- same situastion as "add case"
    exec MUL (eval e₂ ▷ (eval e₁ ▷ s)) ≡⟨ cong (λ x → exec MUL (eval e₂ ▷ x)) (correct e₁ s) ⟩
    exec MUL (eval e₂ ▷ (exec (compile e₁) s)) ≡⟨ cong (λ x → exec MUL x) (correct e₂ (exec (compile e₁) s)) ⟩
    exec MUL (exec (compile e₂) (exec (compile e₁) s)) ∎

  ----------------
  -- If control --
  ----------------

  correct (if b e₁ e₂) s = begin
    eval (if b e₁ e₂) ▷ s ≡⟨ cong (λ x → x ▷ s) (eval-if b) ⟩ -- congruence of evaluating the "if" constructor
    (if (eval b) then (eval e₁) else (eval e₂)) ▷ s ≡⟨ ▷-distributivity b e₁ e₂ s ⟩ -- properity for distribute the "▷" operator
    if (eval b) then (eval e₁ ▷ s) else (eval e₂ ▷ s) ≡⟨ cong (λ x →  if (eval b) then (eval e₁ ▷ s) else x) (correct e₂ s) ⟩ -- apply inductive hypothesis on "(eval e₂ ▷ s)"
    if (eval b) then (eval e₁ ▷ s) else (exec (compile e₂) s) ≡⟨ cong (λ x →  if (eval b) then x else (exec (compile e₂) s)) (correct e₁ s) ⟩ -- apply inductive hypothesis on "(eval e₁ ▷ s)"
    if (eval b) then (exec (compile e₁) s) else (exec (compile e₂) s) ≡⟨ exec-if (eval b) (compile e₁) (compile e₂) s ⟩ -- congruence of executing the "if" constructor
    exec (IF (compile e₁) (compile e₂)) (eval b ▷ s) ≡⟨ cong (λ x →  exec (IF (compile e₁) (compile e₂)) x) (correct b s) ⟩ -- apply the inductive hypothesis on "(eval b ▷ s)"
    exec (IF (compile e₁) (compile e₂)) (exec (compile b) s) ∎
      {-
        It seems that if you use the implicit arguments for these properties, Agda is not sure about the types in the
        demonstration, claiming that it can't resolve some contraints about the types.
        The solution is to explixit the arguments, even if they are useless for showing the validity of these properties.
      -}
      where eval-if : (b : Exp Bool) {e₁ e₂ : Exp T} → eval (if b e₁ e₂) ≡ if (eval b) then (eval e₁) else (eval e₂)
            eval-if b with (eval b)
            ... | false = refl
            ... | true  = refl
            
            ▷-distributivity : (b : Exp Bool) (e₁ e₂ : Exp T) (s : Stack S) →((if eval b then eval e₁ else eval e₂) ▷ s) ≡ (if eval b then eval e₁ ▷ s else (eval e₂ ▷ s))
            ▷-distributivity b e₁ e₂ s with eval b
            ... | false = refl
            ... | true  = refl

            exec-if : (b : Bool) (c₁ c₂ : Code S S') (s : Stack S) → if b then exec c₁ s else exec c₂ s ≡ exec (IF c₁ c₂) (b ▷ s)
            exec-if false c₁ c₂ s = refl
            exec-if true c₁ c₂ s  = refl

