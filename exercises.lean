import standard

namespace sec_3_5

example (em : ∀ p : Prop, p ∨ ¬p) : ∀ p : Prop, ¬¬p → p :=
  take p : Prop,
  suppose ¬¬p,
  have p ∨ ¬p, from em p,
  show p, from or.elim `p ∨ ¬ p` (
    suppose p,
    `p`
  ) (
    suppose ¬p,
    absurd `¬p` `¬¬p`
  )

example (dne : ∀ p : Prop, ¬¬p → p) : ∀ p : Prop, p ∨ ¬p :=
  take p : Prop,
  have ¬¬(p ∨ ¬p), from (
    not.intro (
      suppose ¬(p ∨ ¬p),
      have ¬p, from (
        not.intro (
          suppose p,
          absurd (or.inl `p`) `¬(p ∨ ¬p)`
        )
      ),
      absurd (or.inr `¬p`) `¬(p ∨ ¬p)`
    )
  ),
  show p ∨ ¬p, from dne _ `¬¬(p ∨ ¬p)`

end sec_3_5

namespace sec_3_6

open classical

variables p q r s : Prop

example : p ∧ q ↔ q ∧ p :=
  have lem : ∀ t u : Prop, t ∧ u → u ∧ t, from (
    take t u : Prop,
    assume H : t ∧ u,
    have t, from and.left H,
    have u, from and.right H,
    show u ∧ t, from and.intro `u` `t`
  ),
  iff.intro (
    lem p q
  ) (
    lem q p
  )

example : p ∨ q ↔ q ∨ p :=
  have lem : ∀ t u : Prop, t ∨ u → u ∨ t, from (
    take t u : Prop,
    suppose t ∨ u,
    show u ∨ t, from or.elim `t ∨ u` (
      suppose t,
      or.inr `t`
    ) (
      suppose u,
      or.inl `u`
    )
  ),
  iff.intro (
    lem p q
  ) (
    lem q p
  )

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  iff.intro (
    assume H : (p ∧ q) ∧ r,
    have p, from and.left (and.left H),
    have q, from and.right (and.left H),
    have r, from and.right H,
    show p ∧ (q ∧ r), from and.intro `p` (and.intro `q` `r`)
  ) (
    assume H : p ∧ (q ∧ r),
    have p, from and.left H,
    have q, from and.left (and.right H),
    have r, from and.right (and.right H),
    show (p ∧ q) ∧ r, from and.intro (and.intro `p` `q`) `r`
  )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  iff.intro (
    suppose (p ∨ q) ∨ r,
    show p ∨ (q ∨ r), from or.elim this (
      suppose p ∨ q,
      or.elim this (
        suppose p,
        or.inl `p`
      ) (
        suppose q,
        or.inr (or.inl `q`)
      )
    ) (
      suppose r,
      or.inr (or.inr `r`)
    )
  ) (
    suppose p ∨ (q ∨ r),
    show (p ∨ q) ∨ r, from or.elim this (
      suppose p,
      or.inl (or.inl `p`)
    ) (
      suppose q ∨ r,
      or.elim this (
        suppose q,
        or.inl (or.inr `q`)
      ) (
        suppose r,
        or.inr `r`
      )
    )
  )

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  iff.intro (
    assume H : p ∧ (q ∨ r),
    have p, from and.left H,
    have q ∨ r, from and.right H,
    show (p ∧ q) ∨ (p ∧ r), from or.elim `q ∨ r` (
      suppose q,
      or.inl (and.intro `p` `q`)
    ) (
      suppose r,
      or.inr (and.intro `p` `r`)
    )
  ) (
    suppose (p ∧ q) ∨ (p ∧ r),
    show p ∧ (q ∨ r), from or.elim this (
      suppose p ∧ q,
      have p, from and.left `p ∧ q`,
      have q, from and.right `p ∧ q`,
      and.intro `p` (or.inl `q`)
    ) (
      suppose p ∧ r,
      have p, from and.left `p ∧ r`,
      have r, from and.right `p ∧ r`,
      and.intro `p` (or.inr `r`)
    )
  )

example : p → q → r ↔ p ∧ q → r :=
  iff.intro (
    assume H : p → q → r,
    assume Hpq : p ∧ q,
    have p, from and.left Hpq,
    have q, from and.right Hpq,
    show r, from H `p` `q`
  ) (
    assume H : p ∧ q → r,
    suppose p,
    suppose q,
    show r, from H (and.intro `p` `q`)
  )

example : p ∨ q → r ↔ (p → r) ∧ (q → r) :=
  iff.intro (
    assume H : p ∨ q → r,
    and.intro (
      suppose p,
      show r, from H (or.inl `p`)
    ) (
      suppose q,
      show r, from H (or.inr `q`)
    )
  ) (
    assume H : (p → r) ∧ (q → r),
    have p → r, from and.left H,
    have q → r, from and.right H,
    suppose p ∨ q,
    show r, from or.elim `p ∨ q` (
      suppose p,
      `p → r` `p`
    ) (
      suppose q,
      `q → r` `q`
    )
  )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  iff.intro (
    assume H : ¬(p ∨ q),
    and.intro (
      show ¬p, from not.intro (
        suppose p,
        absurd (or.inl `p`) H
      )
    ) (
      show ¬q, from not.intro (
        suppose q,
        absurd (or.inr `q`) H
      )
    )
  ) (
    assume H : ¬p ∧ ¬q,
    have ¬p, from and.left H,
    have ¬q, from and.right H,
    show ¬(p ∨ q), from not.intro (
      suppose p ∨ q,
      or.elim `p ∨ q` (
        suppose p,
        absurd `p` `¬p`
      ) (
        suppose q,
        absurd `q` `¬q`
      )
    )
  )

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  suppose ¬p ∨ ¬q,
  show ¬(p ∧ q), from not.intro (
    assume H : p ∧ q,
    have p, from and.left H,
    have q, from and.right H,
    or.elim `¬p ∨ ¬q` (
      suppose ¬p,
      absurd `p` `¬p`
    ) (
      suppose ¬q,
      absurd `q` `¬q`
    )
  )

example : ¬(p ∧ ¬p) :=
  not.intro (
    assume H : p ∧ ¬p,
    have p, from and.left H,
    have ¬p, from and.right H,
    absurd `p` `¬p`
  )

example : p ∧ ¬q → ¬(p → q) :=
  assume H : p ∧ ¬q,
  have p, from and.left H,
  have ¬q, from and.right H,
  show ¬(p → q), from not.intro (
    suppose p → q,
    absurd (`p → q` `p`) `¬q`
  )

example : ¬p → p → q :=
  suppose ¬p,
  suppose p,
  absurd `p` `¬p`

example : (¬p ∨ q) → p → q :=
  suppose ¬p ∨ q,
  suppose p,
  show q, from or.elim `¬p ∨ q` (
    suppose ¬p,
    absurd `p` `¬p`
  ) (
    suppose q,
    `q`
  )

example : p ∨ false ↔ p :=
  iff.intro (
    suppose p ∨ false,
    show p, from or.elim `p ∨ false` (
      suppose p,
      `p`
    ) (
      suppose false,
      false.elim `false`
    )
  ) (
    suppose p,
    show p ∨ false, from or.inl `p`
  )

example : p ∧ false ↔ false :=
  iff.intro (
    suppose p ∧ false,
    show false, from and.right `p ∧ false`
  ) (
    suppose false,
    have p, from false.elim `false`,
    show p ∧ false, from and.intro `p` `false`
  )

example : ¬(p ↔ ¬p) :=
  not.intro (
    assume H : p ↔ ¬p,
    have p → ¬p, from iff.mp H,
    have ¬p → p, from iff.mpr H,
    have ¬p, from not.intro (
      suppose p,
      absurd `p` (`p → ¬p` `p`)
    ),
    absurd (`¬p → p` `¬p`) `¬p`
  )

example : (p → q) → (¬q → ¬p) :=
  suppose p → q,
  suppose ¬q,
  show ¬p, from not.intro (
    suppose p,
    absurd (`p → q` `p`) `¬q`
  )

example : (p → r ∨ s) → (p → r) ∨ (p → s) :=
  assume H : p → r ∨ s,
  show (p → r) ∨ (p → s), from by_cases (
    suppose p,
    have r ∨ s, from H `p`,
    or.elim `r ∨ s` (
      suppose r,
      have p → r, from (suppose p, `r`),
      or.inl `p → r`
    ) (
      suppose s,
      have p → s, from (suppose p, `s`),
      or.inr `p → s`
    )
  ) (
    suppose ¬p,
    have p → r, from (
      suppose p,
      absurd `p` `¬p`
    ),
    or.inl `p → r`
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  assume H : ¬(p ∧ q),
  show ¬p ∨ ¬q, from by_cases (
    suppose p,
    have ¬q, from not.intro (
      suppose q,
      absurd (and.intro `p` `q`) H
    ),
    or.inr `¬q`
  ) (
    suppose ¬p,
    or.inl `¬p`
  )

example : ¬(p → q) → p ∧ ¬q :=
  assume H : ¬(p → q),
  show p ∧ ¬q, from by_cases (
    suppose p,
    have ¬q, from not.intro (
      suppose q,
      have p → q, from (suppose p, `q`),
      absurd `p → q` H
    ),
    and.intro `p` `¬q`
  ) (
    suppose ¬p,
    have p → q, from (
      suppose p,
      absurd `p` `¬p`
    ),
    absurd `p → q` H
  )

example : (p → q) → ¬p ∨ q :=
  suppose p → q,
  show ¬p ∨ q, from by_cases (
    suppose p,
    have q, from `p → q` `p`,
    or.inr `q`
  ) (
    suppose ¬p,
    or.inl `¬p`
  )

example : (¬q → ¬p) → (p → q) :=
  assume H : ¬q → ¬p,
  suppose p,
  show q, from by_contradiction (
    suppose ¬q,
    have ¬p, from H `¬q`,
    absurd `p` `¬p`
  )

example : p ∨ ¬p := em p

example : ((p → q) → p) → p :=
  assume H : (p → q) → p,
  show p, from by_cases (
    suppose p,
    `p`
  ) (
    suppose ¬p,
    have p → q, from (
      suppose p,
      absurd `p` `¬p`
    ),
    have p, from H `p → q`,
    absurd `p` `¬p`
  )
  
end sec_3_6
