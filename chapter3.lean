print "\n Prop in Lean \n"

check Prop
check Type.{0} -- same as above

theorem HilbertS {P Q R : Prop}
: (P → Q → R) → (P → Q) → P → R
:=
assume g,
assume f,
assume x,
show R, from g x (f x)

check HilbertS

check fun (A : Type) (a b : A), a = b


constant A : Prop

theorem p1 : A → A → A :=
assume Ha1 : A,
assume Ha2 : A,
show A, from Ha1

theorem p2 : A → A → A :=
assume Ha1 : A,
assume Ha2 : A,
show A, from Ha2

check p1
check p2

example : p1 = p2 := rfl
-- p1 と p2 は別の証明だが等号を示せる。

-- ここまで初回の内容

section sec3_5

-- em (排中律) と dne (二重否定の除去) の同値性を示す。

example (em : ∀ p : Prop, p ∨ ¬p) : ∀ p : Prop, ¬¬p → p :=
take p : Prop,
assume Hnnp : ¬¬p,
show p, from or.elim (em p) (
  assume Hp : p,
  Hp
) (
  assume Hnp : ¬p,
  absurd Hnp Hnnp
)

example (dne : ∀ p : Prop, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
take p : Prop,
have Hnn : ¬¬(p ∨ ¬p), from not.intro (
  assume Hn : ¬(p ∨ ¬p),
  have Hnp : ¬p, from not.intro (
    assume Hp : p,
    absurd (or.inl Hp) Hn
  ),
  absurd (or.inr Hnp) Hn
),
show p ∨ ¬p, from dne _ Hnn

end sec3_5

section sec3_6

open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
have and_comm : ∀ r s : Prop, r ∧ s → s ∧ r, from
  assume r s : Prop,
  assume Hrs : r ∧ s,
  have Hr : r, from and.left Hrs,
  have Hs : s, from and.right Hrs,
  show s ∧ r, from and.intro Hs Hr,
iff.intro (and_comm p q) (and_comm q p)

example : p ∨ q ↔ q ∨ p :=
have or_comm : ∀ r s : Prop, r ∨ s → s ∨ r, from
  assume r s : Prop,
  assume Hrs : r ∨ s,
  show s ∨ r, from
    or.elim Hrs
      (assume Hr : r, or.inr Hr)
      (assume Hs : s, or.inl Hs),
iff.intro (or_comm p q) (or_comm q p)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro (
  assume H : (p ∧ q) ∧ r,
  have Hp : p, from and.left (and.left H),
  have Hq : q, from and.right (and.left H),
  have Hr : r, from and.right H,
  show p ∧ (q ∧ r), from and.intro Hp (and.intro Hq Hr)
) (
  assume H : p ∧ (q ∧ r),
  have Hp : p, from and.left H,
  have Hq : q, from and.left (and.right H),
  have Hr : r, from and.right (and.right H),
  show (p ∧ q) ∧ r, from and.intro (and.intro Hp Hq) Hr
)

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro (
  assume H : p ∧ (q ∨ r),
  have Hp : p, from and.left H,
  have Hqr : q ∨ r, from and.right H,
  show (p ∧ q) ∨ (p ∧ r), from or.elim Hqr
    (assume Hq : q, or.inl (and.intro Hp Hq))
    (assume Hr : r, or.inr (and.intro Hp Hr))
) (
  assume H : (p ∧ q) ∨ (p ∧ r),
  show p ∧ (q ∨ r), from or.elim H (
    assume Hpq : p ∧ q,
    have Hp : p, from and.left Hpq,
    have Hq : q, from and.right Hpq,
    and.intro Hp (or.inl Hq)
  ) (
    assume Hpr : p ∧ r,
    have Hp : p, from and.left Hpr,
    have Hr : r, from and.right Hpr,
    and.intro Hp (or.inr Hr)
  )
)

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro (
  assume H : p ∨ (q ∧ r),
  show (p ∨ q) ∧ (p ∨ r), from or.elim H (
    assume Hp : p,
    and.intro (or.inl Hp) (or.inl Hp)
  ) (
    assume Hqr : q ∧ r,
    have Hq : q, from and.left Hqr,
    have Hr : r, from and.right Hqr,
    and.intro (or.inr Hq) (or.inr Hr)
  )
) (
  assume H : (p ∨ q) ∧ (p ∨ r),
  have Hpq : p ∨ q, from and.left H,
  have Hpr : p ∨ r, from and.right H,
  show p ∨ (q ∧ r), from
    or.elim Hpq (
      assume Hp : p,
      or.inl Hp
    ) (
      assume Hq : q,
      or.elim Hpr (
        assume Hp : p,
        or.inl Hp
      ) (
        assume Hr : r,
        or.inr (and.intro Hq Hr)
      )
    )
)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro (
  assume H : p → q → r,
  assume Hpq : p ∧ q,
  have Hp : p, from and.left Hpq,
  have Hq : q, from and.right Hpq,
  show r, from H Hp Hq
) (
  assume H : p ∧ q → r,
  assume Hp : p,
  assume Hq : q,
  show r, from H (and.intro Hp Hq)
)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro (
  assume H : p ∨ q → r,
  show (p → r) ∧ (q → r), from and.intro (
    assume Hp : p,
    H (or.inl Hp)
  ) (
    assume Hq : q,
    H (or.inr Hq)
  )
) (
  assume H : (p → r) ∧ (q → r),
  have Hpr : p → r, from and.left H,
  have Hqr : q → r, from and.right H,
  assume Hpq : p ∨ q,
  show r, from or.elim Hpq (
    assume Hp : p, Hpr Hp
  ) (
    assume Hq : q, Hqr Hq
  )
)

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro (
  assume H : ¬(p ∨ q),
  show ¬p ∧ ¬q, from and.intro (
    not.intro (
      assume Hp : p,
      absurd (or.inl Hp) H
    )
  ) (
    not.intro (
      assume Hq : q,
      absurd (or.inr Hq) H
    )
  )
) (
  assume H : ¬p ∧ ¬q,
  have Hnp : ¬p, from and.left H,
  have Hnq : ¬q, from and.right H,
  show ¬(p ∨ q), from not.intro (
    assume Hpq : p ∨ q,
    or.elim Hpq (
      assume Hp : p,
      absurd Hp Hnp
    ) (
      assume Hq : q,
      absurd Hq Hnq
    )
  )
)

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume H : ¬p ∨ ¬q,
show ¬(p ∧ q), from not.intro (
  assume Hpq : p ∧ q,
  have Hp : p, from and.left Hpq,
  have Hq : q, from and.right Hpq,
  or.elim H (
    assume Hnp : ¬p,
    absurd Hp Hnp
  ) (
    assume Hnq : ¬q,
    absurd Hq Hnq
  )
)

example : ¬(p ∧ ¬ p) :=
not.intro (
  assume H : p ∧ ¬p,
  have Hp : p, from and.left H,
  have Hnp : ¬p, from and.right H,
  absurd Hp Hnp
)

example : p ∧ ¬q → ¬(p → q) :=
assume H : p ∧ ¬q,
have Hp : p, from and.left H,
have Hnq : ¬q, from and.right H,
show ¬(p → q), from not.intro (
  assume Hpq : p → q,
  absurd (Hpq Hp) Hnq
)

example : ¬p → (p → q) :=
assume Hnp : ¬p,
assume Hp : p,
show q, from absurd Hp Hnp

example : (¬p ∨ q) → (p → q) :=
assume H : ¬p ∨ q,
assume Hp : p,
show q, from or.elim H (
  assume Hnp : ¬p,
  absurd Hp Hnp
) (
  assume Hq,
  Hq
)

example : p ∨ false ↔ p :=
iff.intro (
  assume H : p ∨ false,
  show p, from or.elim H (
    assume Hp : p,
    Hp
  ) (
    assume Hf : false,
    false.elim Hf
  )
) (
  assume Hp : p,
  show p ∨ false, from or.inl Hp
)

example : p ∧ false ↔ false :=
iff.intro (
  assume H : p ∧ false,
  show false, from and.right H
) (
  assume Hf : false,
  show p ∧ false, from false.elim Hf
)

example : ¬(p ↔ ¬p) :=
not.intro (
  assume H : p ↔ ¬p,
  have Hnp : ¬p, from not.intro (
    assume Hp : p,
    absurd Hp (iff.mp H Hp)
  ),
  show false, from absurd (iff.mpr H Hnp) Hnp
)

example : (p → q) → (¬q → ¬p) :=
assume H : p → q,
assume Hnq : ¬q,
show ¬p, from not.intro (
  assume Hp : p,
  absurd (H Hp) Hnq
)

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume H : p → r ∨ s,
show (p → r) ∨ (p → s), from by_cases (
  assume Hr : r,
  or.inl (
    assume Hp : p,
    Hr
  )
) (
  assume Hnr : ¬r,
  or.inr (
    assume Hp : p,
    show s, from or.elim (H Hp) (
      assume Hr : r,
      absurd Hr Hnr
    ) (
      assume Hs : s,
      Hs
    )
  )
)

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume H : ¬(p ∧ q),
show ¬p ∨ ¬q, from by_cases (
  assume Hp : p,
  have Hnq : ¬q, from not.intro (
    assume Hq : q,
    absurd (and.intro Hp Hq) H
  ),
  or.inr Hnq
) (
  assume Hnp : ¬p,
  or.inl Hnp
)

example : ¬(p → q) → p ∧ ¬q :=
assume H : ¬(p → q),
and.intro (
  show p, from by_cases (
    assume Hp : p,
    Hp
  ) (
    assume Hnp : ¬p,
    have Hpq : p → q, from (
      assume Hp : p,
      absurd Hp Hnp
    ),
    absurd Hpq H
  )
) (
  show ¬q, from not.intro (
    assume Hq : q,
    have Hpq : p → q, from (
      assume Hp : p,
      Hq
    ),
    absurd Hpq H
  )
)

example : (p → q) → (¬p ∨ q) :=
assume Hpq : p → q,
show ¬p ∨ q, from by_cases (
  assume Hp : p,
  or.inr (Hpq Hp)
) (
  assume Hnp : ¬p,
  or.inl Hnp
)

example : (¬q → ¬p) → (p → q) :=
assume H : ¬q → ¬p,
assume Hp : p,
show q, from by_contradiction (
  assume Hnq : ¬q,
  absurd Hp (H Hnq)
)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
assume H : (p → q) → p,
show p, from by_cases (
  assume Hp : p,
  Hp
) (
  assume Hnp : ¬p,
  have Hpq : p → q, from (
    assume Hp : p,
    absurd Hp Hnp
  ),
  H Hpq
)

end sec3_6
