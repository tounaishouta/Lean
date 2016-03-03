import standard

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
