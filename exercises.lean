import standard

namespace sec_2_4

open prod

definition curry {A B C : Type} (f : A × B → C) : A → B → C :=
  λ a : A, λ b : B, f (a, b)

definition uncurry {A B C : Type} (f : A → B → C) : A × B → C :=
  λ p : A × B, f (pr₁ p) (pr₂ p)

end sec_2_4

namespace sec_3_5

open function

example (em : ∀ p : Prop, p ∨ ¬p) : ∀ p : Prop, ¬¬p → p :=
  take p,
  suppose ¬¬p,
  or.elim (em p) id (not.elim `¬¬p`)

example (dne : ∀ p : Prop, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
  take p,
  dne (p ∨ ¬p)
    (not.intro
      (assume H : ¬(p ∨ ¬p),
        have ¬p, from not.intro (not.elim H ∘ or.inl),
        absurd (or.inr `¬p`) H))

end sec_3_5

namespace sec_3_6

open classical
open function

variables p q r s : Prop

example : p ∧ q ↔ q ∧ p :=
  iff.intro
    (and.rec (suppose p, suppose q, and.intro `q` `p`))
    (and.rec (suppose q, suppose p, and.intro `p` `q`))

example : p ∨ q ↔ q ∨ p :=
  iff.intro
    (or.rec or.inr or.inl)
    (or.rec or.inr or.inl)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro
    (and.rec
      (and.rec
        (suppose p, suppose q, suppose r, and.intro `p` (and.intro `q` `r`))))
    (and.rec
      (suppose p,
        and.rec (suppose q, suppose r, and.intro (and.intro `p` `q`) `r`)))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro
    (or.rec (or.rec or.inl (or.inr ∘ or.inl))
            (or.inr ∘ or.inr))
    (or.rec (or.inl ∘ or.inl)
            (or.rec (or.inl ∘ or.inr) or.inr))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro
    (and.rec
      (suppose p,
        or.rec (suppose q, or.inl (and.intro `p` `q`))
               (suppose r, or.inr (and.intro `p` `r`))))
    (or.rec (and.rec (suppose p, suppose q, and.intro `p` (or.inl `q`)))
            (and.rec (suppose p, suppose r, and.intro `p` (or.inr `r`))))

example : (p → q → r) ↔ (p ∧ q → r) :=
  iff.intro
    and.rec
    (assume H, suppose p, suppose q, H (and.intro `p` `q`))

example : (p ∨ q → r) ↔ (p → r) ∧ (q → r) :=
  iff.intro
    (assume H, and.intro (H ∘ or.inl) (H ∘ or.inr))
    (and.rec or.rec)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro
    (assume H,
      (and.intro
        (not.intro (not.elim H ∘ or.inl))
        (not.intro (not.elim H ∘ or.inr))))
    (and.rec
      (suppose ¬p, suppose ¬q,
        not.intro (or.rec (not.elim `¬p`) (not.elim `¬q`))))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  or.rec
    (suppose ¬p, not.intro (not.elim `¬p` ∘ and.left))
    (suppose ¬q, not.intro (not.elim `¬q` ∘ and.right))

example : ¬(p ∧ ¬p) :=
  not.intro (and.rec absurd)

example : p ∧ ¬q → ¬(p → q) :=
  and.rec
    (suppose p, suppose ¬q,
      not.intro (assume H, absurd (H `p`) `¬q`))

example : ¬p → p → q :=
  not.elim

example : (¬p ∨ q) → p → q :=
  or.rec
    not.elim
    (suppose q, suppose p, `q`)

example : p ∨ false ↔ p :=
  iff.intro
    (or.rec id false.elim)
    or.inl

example : p ∧ false ↔ false :=
  iff.intro
    and.right
    false.elim

example : ¬(p ↔ ¬p) :=
  not.intro
    (assume H,
      have ¬p, from not.intro (suppose p, absurd `p` (iff.mp H `p`)),
      absurd (iff.mpr H `¬p`) `¬p`)

example : (p → q) → (¬q → ¬p) :=
  assume H, suppose ¬q, not.intro (not.elim `¬q` ∘ H)

example : (p → r ∨ s) → (p → r) ∨ (p → s) :=
  assume H,
  or.elim (em r)
    (suppose r,
      or.inl (suppose p, `r`))
    (suppose ¬r,
      or.inr
        (suppose p,
          or.elim (H `p`) (not.elim `¬r`) id))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume H,
  or.elim (em p)
    (suppose p,
      or.inr (not.intro (not.elim H ∘ and.intro `p`)))
    or.inl

example : ¬(p → q) → p ∧ ¬q :=
  assume H,
  or.elim (em p)
    (suppose p,
      have ¬q, from
        not.intro
          (suppose q,
            have p → q, from suppose p, `q`,
            absurd `p → q` H),
      and.intro `p` `¬q`)
    (suppose ¬p,
      have p → q, from suppose p, absurd `p` `¬p`,
      absurd `p → q` H)

example : (p → q) → ¬p ∨ q :=
  assume H,
  or.elim (em p)
    (or.inr ∘ H)
    or.inl

example : (¬q → ¬p) → (p → q) :=
  assume H,
  suppose p,
  or.elim (em q) id (absurd `p` ∘ H)

example : p ∨ ¬p := em p

example : ((p → q) → p) → p :=
  assume H : (p → q) → p,
  or.elim (em p)
    id
    (suppose ¬p,
      have p → q, from not.elim `¬p`,
      absurd (H `p → q`) `¬p`)

end sec_3_6

namespace sec_4_1

open classical

variables (A : Type) (p q : A → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  iff.intro
    (assume H,
      and.intro
        (take x, and.left (H x))
        (take x, and.right (H x)))
    (and.rec
      (assume Hp Hq,
        take x, and.intro (Hp x) (Hq x)))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  assume H,
  assume Hp,
  take x,
  H x (Hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  or.rec
    (assume H, take x, or.inl (H x))
    (assume H, take x, or.inr (H x))

example : A → ((∀ x : A, r) ↔ r) :=
  take a,
  iff.intro
    (assume H, H a)
    (suppose r, take x, `r`)
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  iff.intro
    (assume H,
      or.elim (em r)
        or.inr
        (suppose ¬r,
          or.inl
            (take x,
              or.elim (H x)
                id
                (not.elim `¬r`))))
    (or.rec
      (assume H, take x, or.inl (H x))
      (suppose r, take x, or.inr `r`))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  iff.intro
    (assume H, suppose r, take x, H x `r`)
    (assume H, take x, suppose r, H `r` x)

variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬(shaves x x)) : false :=
  have lem : ∀ {P : Prop}, (P ↔ ¬P) → false, from
    take P,
    assume H,
    have ¬P, from
      not.intro
        (suppose P,
          not.elim (iff.mp H `P`) `P`),
    not.elim `¬P` (iff.mpr H `¬P`),
  lem (H barber)

end sec_4_1

namespace sec_4_5

open function
open classical

variables (A : Type) (p q : A → Prop) (a : A) (r : Prop)

example : (∃ x : A, r) → r :=
  Exists.rec (take x, suppose r, `r`)

example : r → (∃ x : A, r) :=
  Exists.intro a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (Exists.rec
      (take x,
        (and.rec
          (suppose p x,
            suppose r,
              and.intro
                (Exists.intro x `p x`)
                `r`))))
    (and.rec
      (Exists.rec
        (take x,
          suppose p x,
          suppose r,
          Exists.intro x (and.intro `p x` `r`))))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  iff.intro
    (Exists.rec
      (take x,
        or.rec
          (or.inl ∘ Exists.intro x)
          (or.inr ∘ Exists.intro x)))
    (or.rec
      (Exists.rec (take x, Exists.intro x ∘ or.inl))
      (Exists.rec (take x, Exists.intro x ∘ or.inr)))

-- use classical for ←
example : (∀ x, p x) ↔ (¬ ∃ x, ¬ p x) :=
  iff.intro
    (assume H,
      not.intro
        (Exists.rec
          (take x, absurd (H x))))
    (assume H,
      take x,
      by_contradiction
        (not.elim H ∘ Exists.intro x))

-- use classical fro ←
example : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) :=
  iff.intro
    (Exists.rec
      (take x,
        suppose p x,
        not.intro (assume H, not.elim (H x) `p x`)))
    (assume H : ¬ ∀ x, ¬ p x,
      by_contradiction
        (assume G : ¬ ∃ x, p x,
          have K : ∀ x, ¬ p x, from
            take x, not.intro (not.elim G ∘ Exists.intro x),
          not.elim H K))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  iff.intro
    (assume H : ¬ ∃ x, p x,
      take x,
      not.intro (not.elim H ∘ Exists.intro x))
    (assume H : ∀ x, ¬ p x,
      not.intro
        (Exists.rec
          (take x,
            suppose p x,
              not.elim (H x) `p x`)))

-- use classical for →
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  iff.intro
    (assume H : ¬ ∀ x, p x,
      by_contradiction
        (assume G : ¬ ∃ x, ¬ p x,
          have K : ∀ x, p x, from
            take x,
              by_contradiction (not.elim G ∘ Exists.intro x),
          not.elim H K))
    (Exists.rec
      (take x,
        suppose ¬ p x,
        not.intro
          (assume H : ∀ x, p x,
            not.elim `¬ p x` (H x))))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  iff.intro
    Exists.rec
    (assume H : (∃ x, p x) → r,
      take x,
      H ∘ Exists.intro x)

-- use classical and (a : A)
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  iff.intro
    (Exists.rec
      take x,
      assume H : p x → r,
      assume G : ∀ x, p x,
      H (G x))
    (assume H : (∀ x, p x) → r,
      or.elim (em (∃ x, ¬ p x))
        (Exists.rec
          (take x,
            suppose ¬ p x,
            Exists.intro x
              (suppose p x,
                not.elim `¬ p x` `p x`)))
        (assume G : ¬ ∃ x, ¬ p x,
          have K : ∀ x, p x, from
            take x,
            by_contradiction
              (not.elim G ∘ Exists.intro x),
          have r, from H K,
          Exists.intro a (suppose p a, `r`)))

-- use classical and (a : A)
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  iff.intro
    (Exists.rec
      (take x,
        assume H : r → p x,
        Exists.intro x ∘ H))
    (assume H : r → ∃ x, p x,
      or.elim (em r)
        (suppose r,
          exists.elim (H `r`)
            (take x,
              suppose p x,
              exists.intro x (suppose r, `p x`)))
        (suppose ¬ r,
          exists.intro a
            (not.elim `¬ r`)))

end sec_4_5
