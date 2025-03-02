{-# OPTIONS --cubical-compatible #-}

module Accessibility where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Preliminaries
open import CZFBasics
open import CZFAxioms


{-
   Using the function extensionality, we derive the introduction and elimination rules for
   the accessibility predicate Acc with respect to the membership relation on 𝕍

   -- the Acc-introduction rule ("prog" is the abbreviation of "progressive")
   
   prog : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → Acc v) → Acc a

   -- the Acc-elimination rule
   
   Acc-ind : {ℓ : Level} {C : (v : 𝕍) → Acc v → Set ℓ} →
               (IH : (v : 𝕍) (f : (x : index (tc v)) → Acc (pred (tc v) x)) →
                   ((x : index (tc v)) → C (pred (tc v) x) (f x)) → C v (Acc-intro v f)) →
                 (a : 𝕍) (t : Acc a) → C a t
-}


-- the function extensionality

postulate
  fun-ext : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
    ((x : A) → f x ≡ g x) → f ≡ g


-- We first prove the propositional computation rule of the induction principle for transitive closures of sets
-- First we prove the lemma for this propositional computation rule using the function extensionality

tcTIcomp-lem : (a : 𝕍) → {ℓ : Level} → (F : 𝕍 → Set ℓ) (e : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) →
                 (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                 (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡ λ x → ∈-tcTI e (pred (tc a) x)) ×
                 (∈-tcTI-IH e a ≡ λ x → ∈-tcTI e (pred (tc a) x))
tcTIcomp-lem a {ℓ} = ∈-tcTI
                       {F = λ a → (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                    (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                    (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡
                                      λ x → ∈-tcTI e (pred (tc a) x)) ×
                                    (∈-tcTI-IH e a ≡ λ x → ∈-tcTI e (pred (tc a) x))}
                       (Welim (λ a → (∀𝕧∈ (tc a) λ b →
                                       (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                         ((∈-tcTI e b ≡ e b (λ x → ∈-tcTI e (pred (tc b) x))) ×
                                         (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) b ≡
                                           λ x → ∈-tcTI e (pred (tc b) x)) ×
                                         (∈-tcTI-IH e b ≡ λ x → ∈-tcTI e (pred (tc b) x)))) →
                                     (F : 𝕍 → Set ℓ) (e : (w : 𝕍) → (∀𝕧∈ (tc w) λ v → F v) → F w) →
                                       ((∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                       (∈-tcTI (λ v d z → e (pred (tc v) z) (d z)) a ≡
                                         (λ x → ∈-tcTI e (pred (tc a) x))) ×
                                       (∈-tcTI-IH e a ≡ (λ x → ∈-tcTI e (pred (tc a) x)))))
                              λ A f prec IH F e →
                              let sublem-one : (x : index (tc (sup A f))) →
                                                 e (pred (tc (sup A f)) x)
                                                   (∈-tcTI-IH (λ v d z₁ → e (pred (tc v) z₁) (d z₁))
                                                     (sup A f) x) ≡
                                                 ∈-tcTI e (pred (tc (sup A f)) x)
                                  sublem-one = ⊕elim
                                                 (λ x → e (pred (tc (sup A f)) x)
                                                          (∈-tcTI-IH (λ v d z → e (pred (tc v) z) (d z))
                                                                     (sup A f) x) ≡
                                                        ∈-tcTI e (pred (tc (sup A f)) x))
                                                 (λ y → ≡trans
                                                          (transp (λ d → e (f y)
                                                                           (∈-tcTI
                                                                             (λ v d z → e (pred (tc v) z) (d z))
                                                                             (f y)) ≡
                                                                         e (f y) d)
                                                                  (snd (fst (IH (injl y) F e)))
                                                                  refl)
                                                          (≡sym (fst (fst (IH (injl y) F e)))))
                                                 λ (y , c) → ≡trans
                                                               (transp (λ h → e (pred (tc (f y)) c)
                                                                         (∈-tcTI 
                                                                           (λ a d z z₁ →
                                                                             e (pred (tc (pred (tc a) z)) z₁) (d z z₁))
                                                                           (f y) c) ≡
                                                                           e (pred (tc (f y)) c) h)
                                                                       (snd (fst (IH (injr (y , c)) F e)))
                                                                       (transp (λ h → e (pred (tc (f y)) c)
                                                                                        (∈-tcTI {F = λ a → ∀𝕧∈ (tc a)
                                                                                                       λ v → (x : index (tc v)) →
                                                                                                         F (pred (tc v) x)}
                                                                                          (λ v₁ d₁ z₁ →
                                                                                            (λ z →
                                                                                              e (pred (tc (pred (tc v₁) z₁)) z)
                                                                                                (d₁ z₁ z)))
                                                                                          (f y) c) ≡
                                                                                      e (pred (tc (f y)) c) h)
                                                                               (inv-fun-ext
                                                                                 (snd (fst (IH (injl y)
                                                                                   (λ a → ∀𝕧∈ (tc a) λ v → F v)
                                                                                     (λ v d z → e (pred (tc v) z) (d z))))) c)
                                                                               refl))
                                                               (≡sym (fst (fst (IH (injr (y , c)) F e))))
                                  sublem-two : (x : index (tc (sup A f))) →
                                                 ∈-tcTI-IH e (sup A f) x ≡ ∈-tcTI e (pred (tc (sup A f)) x)
                                  sublem-two = ⊕elim
                                                 (λ x → ∈-tcTI-IH e (sup A f) x ≡ ∈-tcTI e (pred (tc (sup A f)) x))
                                                 (λ y → refl)
                                                 λ (y , c) → inv-fun-ext (snd (fst (IH (injl y) F e))) c
                              in (ap (λ d → e (sup A f) d) (fun-ext sublem-two) ,
                                  fun-ext sublem-one) ,
                                  fun-ext sublem-two)
                       a

-- the propositional computation rule of the induction principle for transitive closures of sets

tcTIcomp : {ℓ : Level} {F : 𝕍 → Set ℓ} → (e : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → F v) → F a) (a : 𝕍) →
                 (∈-tcTI e a ≡ e a (λ x → ∈-tcTI e (pred (tc a) x)))
tcTIcomp {F = F} e a = fst (fst (tcTIcomp-lem a F e))


-- Definition of Acc
-- We obtain Acc a ≡ ∀𝕧∈ (tc a) λ v → Acc v from this definition and tcTIcomp

Acc : 𝕍 → Set
Acc = ∈-tcTI λ a IH → (x : index (tc a)) → IH x


-- The equality Acc a ≡ ∀𝕧∈ (tc a) λ v → Acc v enables to derive the introduction rule for Acc

prog : (a : 𝕍) → (∀𝕧∈ (tc a) λ v → Acc v) → Acc a
prog a = transp (λ A → A) (≡sym (tcTIcomp (λ a' IH → (x : index (tc a')) → IH x) a))


-- Transporting in the opposite direction to the case of prog provides the inversion for Acc

Acc-inv : (a : 𝕍) → Acc a → (∀𝕧∈ (tc a) λ v → Acc v)
Acc-inv a = transp (λ A → A) (tcTIcomp (λ a' IH → (x : index (tc a')) → IH x) a)


-- Next we derive the elimination rule for Acc

-- We first prove a lemma for transporting along the equality prog a (Acc-inv a t) ≡ t

transpAcc : {ℓ : Level} {C : (v : 𝕍) → Acc v → Set ℓ} →
              (IH : (v : 𝕍) (f : (x : index (tc v)) → Acc (pred (tc v) x)) →
                  ((x : index (tc v)) → C (pred (tc v) x) (f x)) → C v (prog v f)) →
                (a : 𝕍) (t : Acc a) → C a (prog a (Acc-inv a t)) → C a t
transpAcc {ℓ} {C} IH a t =
  transp (λ s → C a s)
         (transpCancel1 (tcTIcomp (λ a' IH → (x : index (tc a')) → IH x) a) t)

-- the Acc-elimination rule

Acc-ind : {ℓ : Level} {C : (v : 𝕍) → Acc v → Set ℓ} →
             (IH : (v : 𝕍) (f : (x : index (tc v)) → Acc (pred (tc v) x)) →
                 ((x : index (tc v)) → C (pred (tc v) x) (f x)) → C v (prog v f)) →
               (a : 𝕍) (t : Acc a) → C a t
Acc-ind {ℓ} {C} IH =
  ∈-tcTI {F = λ v → (u : Acc v) → C v u}
         (λ v subIH u →
           transpAcc IH v u (IH v (Acc-inv v u) (λ x → subIH x (Acc-inv v u x))))


-- the propositional computation rule for Acc-ind

Acc-comp : {ℓ : Level} {C : (v : 𝕍) → Acc v → Set ℓ} →
             (IH : (v : 𝕍) (f : (x : index (tc v)) → Acc (pred (tc v) x)) →
                 ((x : index (tc v)) → C (pred (tc v) x) (f x)) → C v (prog v f)) →
               (a : 𝕍) (g : (x : index (tc a)) → Acc (pred (tc a) x)) →
                 Acc-ind {C = C} IH a (prog a g) ≡
                 transpAcc {C = C} IH a (prog a g)
                   (IH a (Acc-inv a (prog a g))
                     (λ x → Acc-ind {C = C} IH (pred (tc a) x) (Acc-inv a (prog a g) x)))
Acc-comp {ℓ} {C} IH a g =
  inv-fun-ext (tcTIcomp (λ v subIH u →
                           transpAcc IH v u (IH v (Acc-inv v u) (λ x → subIH x (Acc-inv v u x))))
                        a)
              (prog a g)
