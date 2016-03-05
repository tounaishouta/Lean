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

namespace sec_6_4

open function
open eq

inductive nat : Type :=
| zero : nat
|  succ : nat → nat

namespace nat

definition add (n : nat) : nat → nat :=
  nat.rec
    n
    (λ m add_n_m, succ add_n_m)

notation 0 := zero
infix `+` := add

theorem add_zero (n : nat) : n + 0 = n := rfl

theorem add_succ (n m : nat) : n + succ m = succ (n + m) := rfl

theorem add_assoc (n m : nat) : ∀ k : nat, (n + m) + k = n + (m + k) :=
  nat.rec
    rfl
    (take k,
      assume IH : (n + m) + k = n + (m + k),
      calc (n + m) + succ k
           = succ ((n + m) + k) : add_succ ...
           = succ (n + (m + k)) : IH       ...
           = n + succ (m + k)   : add_succ ...
           = n + (m + succ k)   : add_succ)

theorem zero_add : ∀ m : nat, 0 + m = m :=
  nat.rec
    rfl
    (take m,
      assume IH : 0 + m = m,
      calc 0 + succ m
           = succ (0 + m) : add_succ ...
           = succ m       : IH)

theorem succ_add (n : nat) : ∀ m : nat, succ n + m = succ (n + m) :=
  nat.rec
    rfl
    (take m,
      assume IH : succ n + m = succ (n + m),
      calc succ n + succ m
           = succ (succ n + m)   : add_succ ...
           = succ (succ (n + m)) : IH       ...
           = succ (n + succ m)   : add_succ)

theorem add_comm (n : nat) : ∀ m : nat, n + m = m + n :=
  nat.rec
    (calc n + 0
          = n     : add_zero ...
          = 0 + n : zero_add)
    (take m,
      assume IH : n + m = m + n,
      calc n + succ m
           = succ (n + m) : add_succ ...
           = succ (m + n) : IH       ...
           = succ m + n   : succ_add)

definition mul (n : nat) : nat → nat :=
  nat.rec
    0
    (λ m mul_n_m, mul_n_m + n)

infix `*` := mul

theorem mul_zero (n : nat) : n * 0 = 0 := rfl

theorem mul_succ (n m : nat) : n * (succ m) = n * m + n := rfl

theorem zero_mul : ∀ m : nat, 0 * m = 0 :=
  nat.rec
    rfl
    (take m,
      assume IH : 0 * m = 0,
      calc 0 * succ m
           = 0 * m + 0 : mul_succ ...
           = 0 * m     : add_zero ...
           = 0         : IH)

theorem mul_distrib (n m : nat) : ∀ k : nat, n * (m + k) = n * m + n * k :=
  nat.rec
    (calc n * (m + 0)
          = n * m         : add_zero ...
          = n * m + 0     : add_zero ...
          = n * m + n * 0 : mul_zero)
    (take k,
      assume IH : n * (m + k) = n * m + n * k,
      calc n * (m + succ k)
           = n * succ (m + k)     : add_succ  ...
           = n * (m + k) + n      : mul_succ  ...
           = (n * m + n * k) + n  : IH        ...
           = n * m + (n * k + n)  : add_assoc ...
           = n * m + (n * succ k) : mul_succ)

theorem mul_assoc (n m : nat) : ∀ k : nat, (n * m) * k = n * (m * k) :=
  nat.rec
    (calc (n * m) * 0
          = 0           : mul_zero ...
          = n * 0       : mul_zero ...
          = n * (m * 0) : mul_zero)
    (take k,
      assume IH : (n * m) * k = n * (m * k),
      calc (n * m) * succ k
           = (n * m) * k + n * m : mul_succ    ...
           = n * (m * k) + n * m : IH          ...
           = n * (m * k + m)     : mul_distrib ...
           = n * (m * succ k)    : mul_succ)

theorem succ_mul (n : nat) : ∀ m : nat, succ n * m = n * m + m :=
  nat.rec
    (calc succ n * 0
          = 0         : mul_zero ...
          = 0 + 0     : add_zero ...
          = n * 0 + 0 : mul_zero)
    (take m,
      assume IH : succ n * m = n * m + m,
      calc succ n * succ m
           = succ n * m + succ n   : mul_succ  ...
           = (n * m + m) + succ n  : IH        ...
           = n * m + (m + succ n)  : add_assoc ...
           = n * m + succ (m + n)  : add_succ  ...
           = n * m + succ (n + m)  : add_comm  ...
           = n * m + (n + succ m)  : add_succ  ...
           = (n * m + n) + succ m  : add_assoc ...
           = (n * succ m) + succ m : mul_succ)

theorem mul_comm (n : nat) : ∀ m : nat, n * m = m * n :=
  nat.rec
    (calc n * 0
          = 0     : mul_zero ...
          = 0 * n : zero_mul)
    (take m,
      assume IH : n * m = m * n,
      calc n * succ m
           = n * m + n  : mul_succ ...
           = m * n + n  : IH       ...
           = succ m * n : succ_mul)

definition pred : nat → nat :=
  nat.rec 0 (λ n pred_n, n)

theorem pred_succ (n : nat) : pred (succ n) = n := rfl

theorem succ_pred : ∀ n : nat, n ≠ 0 → succ (pred n) = n :=
  nat.rec
    (suppose 0 ≠ 0,
      absurd rfl `0 ≠ 0`)
    (take n,
      assume IH, -- 使わない
      assume H, -- 使わない
      calc succ (pred (succ n)) = succ n : pred_succ)

end nat

end sec_6_4

namespace sec_6_5

inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A

namespace list

variable {A : Type}

notation h :: t := cons h t

definition append (s t : list A) : list A :=
  list.rec_on s t (λ x s' append_s'_t, x :: append_s'_t)

notation s ++ t := append s t

theorem nil_append (t : list A) : nil ++ t = t := rfl

theorem cons_append (x : A) (s t : list A) : (x :: s) ++ t = x :: (s ++ t) :=
  rfl

theorem append_nil : ∀ t : list A, t ++ nil = t :=
  list.rec
    rfl
    (take x : A,
      take xs : list A,
      assume IH : xs ++ nil = xs,
      calc (x :: xs) ++ nil
           = x :: (xs ++ nil) : cons_append ...
           = x :: xs          : IH)
  
theorem append_assoc (r s t : list A) : (r ++ s) ++ t = r ++ (s ++ t) :=
  list.rec_on r
    (calc (nil ++ s) ++ t
          = s ++ t          : nil_append ...
          = nil ++ (s ++ t) : nil_append)
    (take x,
      take r,
      assume IH : (r ++ s) ++ t = r ++ (s ++ t),
      calc ((x :: r) ++ s) ++ t
           = (x :: (r ++ s)) ++ t : cons_append ...
           = x :: ((r ++ s) ++ t) : cons_append ...
           = x :: (r ++ (s ++ t)) : IH          ...

           = (x :: r) ++ (s ++ t) : cons_append)
end list

end sec_6_5
