import data.nat

section sec4_1_1

variables (A : Type) (p q : A → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro (
  assume H : ∀ x : A, p x ∧ q x,
  and.intro (
    take x : A,
    show p x, from and.left (H x)
  ) (
    take x : A,
    show q x, from and.right (H x)
  )
) (
  assume H : (∀ x : A, p x) ∧ (∀ x : A, q x),
  take x : A,
  show p x ∧ q x, from and.intro (and.left H x) (and.right H x)
)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume Hpq : ∀ x : A, p x → q x,
assume Hp : ∀ x : A, p x,
take x : A,
show q x, from Hpq x (Hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
assume H,
or.elim H (
  assume Hp : ∀ x : A, p x,
  take x : A,
  show p x ∨ q x, from or.inl (Hp x)
) (
  assume Hq : ∀ x : A, q x,
  take x : A,
  show p x ∨ q x, from or.inr (Hq x)
)

end sec4_1_1

section sec4_1_2

open classical

variables (A : Type) (p q : A → Prop)
variable r : Prop

example : A → ((∀ x : A, r) ↔ r) :=
take a : A,
iff.intro (
  assume H : ∀ x : A, r,
  show r, from H a
) (
  assume Hr : r,
  take x : A,
  show r, from Hr
)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro (
  assume H : ∀ x : A, p x ∨ r,
  by_cases (
    assume Hr : r,
    show (∀ x : A, p x) ∨ r, from or.inr Hr
  ) (
    assume Hnr : ¬r,
    show (∀ x : A, p x) ∨ r, from or.inl (
      take x : A,
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
  assume H : (∀ x : A, p x) ∨ r,
  or.elim H (
    assume Hp : ∀ x : A, p x,
    take x : A,
    show p x ∨ r, from or.inl (Hp x)
  ) (
    assume Hr : r,
    take x : A,
    show p x ∨ r, from or.inr Hr
  )
)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro (
  assume H : ∀ x : A, r → p x,
  assume Hr : r,
  take x : A,
  show p x, from H x Hr
) (
  assume H : r → ∀ x : A, p x,
  take x : A,
  assume Hr : r,
  show p x, from (H Hr) x
)

end sec4_1_2

section sec4_1_3

variables (men : Type) (barber : men) (shaves : men → men → Prop)

example (H : ∀ x : men, shaves barber x ↔ ¬shaves x x) : false :=
have Lem1 : ∀ (p : Prop), ¬(p ↔ ¬p), from (
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
absurd (H barber) (Lem1 (shaves barber barber))

end sec4_1_3

section sec4_3

open nat algebra

-- check @left_distrib
-- check @right_distrib
-- check @add.assoc

example (x y : ℕ) : (x + y) * (x + y) = x * x + y * x + x *y + y * y :=
calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y       : left_distrib
  ...               = x * x + y * x + (x + y) * y     : right_distrib
  ...               = x * x + y * x + (x * y + y * y) : right_distrib
  ...               = x * x + y * x + x * y + y * y   : add.assoc

open int

-- find_decl (_ - _) * _ = _ * _ - _ * _
-- check @mul_sub_right_distrib

-- find_decl _ - (_ + _) = _ - _ - _
-- check @sub_add_eq_sub_sub

-- find_decl _ * _ = _ * _, + comm
-- check @mul.comm

-- find_decl _ + _ - _ = _ + (_ - _)
-- check @add_sub_assoc

-- find_decl _ - _ = 0
-- check @sub_self

-- find_decl _ + 0 = _
-- check @add_zero

example (x y : ℤ) : (x - y) * (x + y) = x * x - y * y :=
calc
  (x - y) * (x + y) = x * (x + y) - y * (x + y)       : mul_sub_right_distrib
  ...               = x * x + x * y - y * (x + y)     : left_distrib
  ...               = x * x + x * y - (y * x + y * y) : left_distrib
  ...               = x * x + x * y - y * x - y * y   : sub_add_eq_sub_sub
  ...               = x * x + x * y - x * y - y * y   : mul.comm
  ...               = x * x + (x * y - x * y) - y * y : add_sub_assoc
  ...               = x * x + 0 - y * y               : sub_self
  ...               = x * x - y * y                   : add_zero

end sec4_3

section sec4_5

open classical

variables (A : Type) (p q : A → Prop)
variable a : A
variable r : Prop

example : (∃ x : A, r) → r :=
assume H : ∃ x : A, r,
obtain (w : A) (Hr : r), from H,
show r, from Hr

-- use a
example : r → (∃ x : A, r) :=
assume Hr : r,
show ∃ x : A, r, from exists.intro a Hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro (
  assume H : ∃ x : A, p x ∧ r,
  obtain (w : A) (Hw : p w ∧ r), from H,
  show (∃ x : A, p x) ∧ r, from and.intro (
    exists.intro w (and.left Hw)
  ) (
    and.right Hw
  )
) (
  assume H : (∃ x : A, p x) ∧ r,
  obtain (w : A) (Hw : p w), from and.left H,
  have Hr : r, from and.right H,
  show ∃ x : A, p x ∧ r, from exists.intro w (
    and.intro Hw Hr
  )
)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro (
  assume H : ∃ x : A, p x ∨ q x,
  obtain (w : A) (Hw : p w ∨ q w), from H,
  show (∃ x : A, p x) ∨ (∃ x : A, q x), from or.elim Hw (
    assume Hpw : p w,
    or.inl (exists.intro w Hpw)
  ) (
    assume Hqw : q w,
    or.inr (exists.intro w Hqw)
  )
) (
  assume H : (∃ x : A, p x) ∨ (∃ x : A, q x),
  show ∃ x : A, p x ∨ q x, from or.elim H (
    assume Hp : ∃ x: A, p x,
    obtain (w : A) (Hpw : p w), from Hp,
    exists.intro w (or.inl Hpw)
  ) (
    assume Hq : ∃ x : A, q x,
    obtain (w : A) (Hqw : q w), from Hq,
    exists.intro w (or.inr Hqw)
  )
)

-- use em
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro (
  assume Hap : ∀ x : A, p x,
  show ¬ (∃ x : A, ¬ p x), from not.intro (
    assume Henp : ∃ x : A, ¬ p x,
    obtain (w : A) (Hnpw : ¬ p w), from Henp,
    absurd (Hap w) Hnpw
  )
) (
  assume Hnenp : ¬ (∃ x : A, ¬ p x),
  take x : A,
  show p x, from by_contradiction (
    assume Hnpx : ¬ p x,
    have Henp : ∃ x : A, ¬ p x, from exists.intro x Hnpx,
    absurd Henp Hnenp
  )
)

-- use em
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro (
  assume Hep : ∃ x : A, p x,
  obtain (w : A) (Hpw : p w), from Hep,
  show ¬ (∀ x : A, ¬ p x), from not.intro (
    assume Hanp : ∀ x : A, ¬ p x,
    absurd Hpw (Hanp w)
  )
) (
  assume Hnanp : ¬ (∀ x : A, ¬ p x),
  show ∃ x : A, p x, from by_contradiction (
    assume Hnep : ¬ (∃ x : A, p x),
    have Hanp : ∀ x : A, ¬ p x, from (
      take x : A,
      show ¬ p x, from not.intro (
        assume Hpx : p x,
        absurd (exists.intro x Hpx) Hnep
      )
    ),
    absurd Hanp Hnanp
  )
)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro (
  assume Hnep : ¬ (∃ x : A, p x),
  take x : A,
  show ¬ p x, from not.intro (
    assume Hpx : p x,
    absurd (exists.intro x Hpx) Hnep
  )
) (
  assume Hanp : ∀ x : A, ¬ p x,
  show ¬ (∃ x : A, p x), from not.intro (
    assume Hep : ∃ x : A, p x,
    obtain (w : A) (Hpw : p w), from Hep,
    absurd Hpw (Hanp w)
  )
)

-- use em
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro (
  assume Hnap : ¬ ∀ x : A, p x,
  show ∃ x : A, ¬ p x, from by_contradiction (
    assume Hnenp : ¬ ∃ x : A, ¬ p x,
    have Hap : ∀ x : A, p x, from (
      take x : A,
      show p x, from by_cases (
        assume Hpx : p x,
        Hpx
      ) (
        assume Hnpx : ¬ p x,
        absurd (exists.intro x Hnpx) Hnenp
      )
    ),
    absurd Hap Hnap
  )
) (
  assume Henp : ∃ x : A, ¬ p x,
  obtain (w : A) (Hnpw : ¬ p w), from Henp,
  show ¬ ∀ x : A, p x, from not.intro (
    assume Hap : ∀ x : A, p x,
    absurd (Hap w) (Hnpw)
  )
)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro (
  assume Hapr : ∀ x : A, p x → r,
  assume Hep : ∃ x : A, p x,
  obtain (w : A) (Hpw : p w), from Hep,
  show r, from Hapr w Hpw
) (
  assume Hepr : (∃ x : A, p x) → r,
  take x : A,
  assume Hpx : p x,
  show r, from Hepr (exists.intro x Hpx)
)

-- use em & a
example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro (
  assume Hepr : ∃ x : A, p x → r,
  obtain (w : A) (Hpwr : p w → r), from Hepr,
  assume Hap : ∀ x : A, p x,
  show r, from Hpwr (Hap w)
) (
  assume Hapr : (∀ x : A, p x) → r,
  show ∃ x : A, p x → r, from by_cases (
    assume Henp : ∃ x : A, ¬ p x,
    obtain (w : A) (Hnpw : ¬ p w), from Henp,
    exists.intro w (
      assume Hpw : p w,
      absurd Hpw Hnpw
    )
  ) (
    assume Hnenp : ¬ ∃ x : A, ¬ p x,
    have Hap : ∀ x : A, p x, from (
      take x : A,
      show p x, from by_contradiction (
        assume Hnpx : ¬ p x,
        absurd (exists.intro x Hnpx) Hnenp
      )
    ),
    have Hr : r, from Hapr Hap,
    show ∃ x : A, p x → r, from exists.intro a (
      assume Hpa : p a,
      Hr
    )
  )
)

-- use em & a
example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
iff.intro (
  assume Herp : ∃ x : A, r → p x,
  obtain (w : A) (Hrpw : r → p w), from Herp,
  assume Hr : r,
  show ∃ x : A, p x, from exists.intro w (Hrpw Hr)
) (
  assume Hrep : r → ∃ x : A, p x,
  show ∃ x : A, r → p x, from by_cases (
    assume Hr : r,
    obtain (w : A) (Hpw : p w), from Hrep Hr,
    exists.intro w (
      assume Hr' : r,
      Hpw
    )
  ) (
    assume Hnr : ¬ r,
    exists.intro a (
      assume Hr : r,
      absurd Hr Hnr
    )
  )
)

end sec4_5
