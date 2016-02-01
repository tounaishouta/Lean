section sec4_1_1

variables (A : Type) (p q : A → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro (
  assume H,
  and.intro (
    take x,
    and.left (H x)
  ) (
    take x,
    and.right (H x)
  )
) (
  assume H,
  take x,
  and.intro (and.left H x) (and.right H x)
)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume Hpq,
assume Hp,
take x,
Hpq x (Hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume H,
or.elim H (
  assume Hp,
  take x,
  or.inl (Hp x)
) (
  assume Hq,
  take x,
  or.inr (Hq x)
)

end sec4_1_1

section sec4_1_2

open classical
 
variables (A : Type) (p q : A → Prop)
variable r : Prop

example : A → ((∀ x : A, r) ↔ r) :=
take a,
iff.intro (
  assume H,
  H a
) (
  assume Hr,
  take x,
  Hr
)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro (
  assume H,
  by_cases (
    assume Hr : r,
    or.inr Hr
  ) (
    assume Hnr : ¬r,
    or.inl (
      take x,
      or.elim (H x) (
        assume Hpx : p x,
        Hpx
      ) (
        assume Hr : r,
        absurd Hr Hnr
      )
    )
  )
) (
  assume H,
  or.elim H (
    assume Hp,
    take x,
    or.inl (Hp x)
  ) (
    assume Hr,
    take x,
    or.inr Hr
  )
)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro (
  assume H,
  assume Hr : r,
  take x,
  show p x, from H x Hr
) (
  assume H,
  take x,
  assume Hr : r,
  show p x, from (H Hr) x
)

end sec4_1_2


section sec4_1_3

variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
have Lem1 : ∀ {p : Prop}, ¬(p ↔ ¬p), from (
  assume p : Prop,
  not.intro (
    assume H : p ↔ ¬p,
    have Hnp : ¬p, from (
      not.intro (
        assume Hp : p,
        absurd Hp (iff.mp H Hp)
      )
    ),
    absurd (iff.mpr H Hnp) Hnp
  )
),
absurd (H barber) Lem1

end sec4_1_3
