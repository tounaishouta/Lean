import standard

namespace sec_2_4

open nat

definition double (x : nat) : nat := x + x

definition do_twice (f : nat → nat) (x : nat) : nat := f (f x)

definition quadruple : nat → nat := do_twice double

-- eval quadruple 8
-- 32

definition Do_Twice : ((nat → nat) → (nat → nat)) → ((nat → nat) → (nat → nat))
| Do_Twice F f := F (F f)

-- eval Do_Twice do_twice double 2
-- 32

open prod

definition curry {A B C : Type} : (A × B → C) → (A → B → C)
| curry f a b := f (a, b)

definition uncurry {A B C : Type} : (A → B → C) → (A × B → C)
| uncurry f (a, b) := f a b

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

namespace sec_4_3

open nat

-- check nat.left_distrib
-- check nat.mul_comm
-- check nat.add_comm
-- check nat.mul_sub_right_distrib
-- check nat.add_sub_add_left

example (x y : ℕ) : (x - y) * (x + y) = x * x - y * y :=
  calc (x - y) * (x + y) = x * (x + y) - y * (x + y)         : nat.mul_sub_right_distrib
       ...               = (x * x + x * y) - y * (x + y)     : nat.left_distrib
       ...               = (x * x + x * y) - (y * x + y * y) : nat.left_distrib
       ...               = (x * x + x * y) - (x * y + y * y) : nat.mul_comm
       ...               = (x * y + x * x) - (x * y + y * y) : nat.add_comm
       ...               = x * x - y * y                     : nat.add_sub_add_left

end sec_4_3

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

namespace sec_6_1

inductive bool : Type :=
| ff : bool
| tt : bool

namespace bool

definition band : bool → bool → bool
| band tt tt := tt
| band _  _  := ff

example : band ff ff = ff := rfl
example : band ff tt = ff := rfl
example : band tt ff = ff := rfl
example : band tt ff = ff := rfl

definition bor : bool → bool → bool
| bor ff ff := ff
| bor _  _  := tt

example : bor ff ff = ff := rfl
example : bor ff tt = tt := rfl
example : bor tt ff = tt := rfl
example : bor tt tt = tt := rfl

definition bnot : bool → bool
| bnot ff := tt
| bnot tt := ff

example : bnot ff = tt := rfl
example : bnot tt = ff := rfl

end bool

end sec_6_1

namespace sec_6_2

open function

inductive option (A : Type) : Type :=
| none {} : option A
| some    : A → option A

namespace option

definition maybe {A B : Type} : B → (A → B) → option A → B
| maybe b f oa := option.rec_on oa b f

definition bind {A B : Type} : (A → option B) → option A → option B := maybe none

definition return {A : Type} : A → option A := some

definition mcomp {A B C : Type} : (B → option C) → (A → option B) → (A → option C)
| mcomp g f := λ a : A, bind g (f a)

notation f `=<<` m := bind f m
notation g `<=<` f := mcomp g f

-- モナド則

example (A B : Type) (f : A → option B) (x : A) : (f =<< return x) = f x := rfl

example (A : Type) (m : option A) : (return =<< m) = m :=
  match m with
  | none   := rfl
  | some a := rfl
  end

example (A B C : Type) (f : A → option B) (g : B → option C) (m : option A) : ((g <=< f) =<< m) = (g =<< (f =<< m)) :=
  match m with
  | none   := rfl
  | some a := rfl
  end

definition pfunc (A B : Type) : Type := A → option B

definition pcomp {A B C : Type} : pfunc B C → pfunc A B → pfunc A C := mcomp

variables A B C : Type
variables (f : pfunc A B) (g : pfunc B C) (a : A) (b : B) (c : C)

example : f a = none → pcomp g f a = none :=
  assume H : f a = none,
  calc pcomp g f a = maybe none g (f a) : rfl
       ...         = maybe none g none  : {H} -- なぜ brace が必要?
       ...         = none               : rfl

example : f a = some b → pcomp g f a = g b :=
  assume H : f a = some b,
  calc pcomp g f a = maybe none g (f a)    : rfl
       ...         = maybe none g (some b) : {H}
       ...         = g b                   : rfl

end option

inductive inhabited (A : Type) : Type :=
| mk : A → inhabited A

example : inhabited bool := inhabited.mk bool.ff

example : inhabited nat := inhabited.mk zero

end sec_6_2

namespace sec_6_4

open function
open eq

inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat

notation 0 := zero

definition add : nat → nat → nat
| add n 0        := n
| add n (succ m) := succ (add n m)

infix `+` := add

theorem add_zero : ∀ n : nat, n + 0 = n
| add_zero n := rfl

theorem add_succ : ∀ n m : nat, n + succ m = succ (n + m)
| add_succ n m := rfl

theorem add_assoc : ∀ n m k : nat, (n + m) + k = n + (m + k)
| add_assoc n m 0 :=
  calc (n + m) + 0 = n + m       : add_zero
       ...         = n + (m + 0) : add_zero
| add_assoc n m (succ k) :=
  calc (n + m) + succ k = succ ((n + m) + k) : add_succ
       ...              = succ (n + (m + k)) : add_assoc
       ...              = n + succ (m + k)   : add_succ
       ...              = n + (m + succ k)   : add_succ

theorem zero_add : ∀ m : nat, 0 + m = m
| zero_add 0 :=
  calc 0 + 0 = 0 : add_zero
| zero_add (succ m) :=
  calc 0 + succ m = succ (0 + m) : add_succ
       ...        = succ m       : zero_add

theorem succ_add : ∀ n m : nat, succ n + m = succ (n + m)
| succ_add n 0 :=
  calc succ n + 0 = succ n       : add_zero
       ...        = succ (n + 0) : add_zero
| succ_add n (succ m) :=
  calc succ n + succ m = succ (succ n + m)   : add_succ
       ...             = succ (succ (n + m)) : succ_add
       ...             = succ (n + succ m)   : add_succ

theorem add_comm : ∀ n m : nat, n + m = m + n
| add_comm n 0 :=
  calc n + 0 = n     : add_zero
       ...   = 0 + n : zero_add
| add_comm n (succ m) :=
  calc n + succ m = succ (n + m) : add_succ
       ...        = succ (m + n) : add_comm
       ...        = succ m + n   : succ_add

definition mul : nat → nat → nat
| mul n 0        := 0
| mul n (succ m) := mul n m + n

infix `*` := mul

theorem mul_zero : ∀ n : nat, n * 0 = 0
| mul_zero n := rfl

theorem mul_succ : ∀ n m : nat, n * (succ m) = n * m + n
| mul_succ n m := rfl

theorem zero_mul : ∀ m : nat, 0 * m = 0
| zero_mul 0 :=
  calc 0 * 0 = 0 : mul_zero
| zero_mul (succ m) :=
  calc 0 * succ m = 0 * m + 0 : mul_succ
       ...        = 0 + 0     : zero_mul
       ...        = 0         : add_zero

theorem mul_distrib : ∀ n m k : nat, n * (m + k) = n * m + n * k
| mul_distrib n m 0 :=
  calc n * (m + 0) = n * m         : add_zero
       ...         = n * m + 0     : add_zero
       ...         = n * m + n * 0 : mul_zero
| mul_distrib n m (succ k) :=
  calc n * (m + succ k) = n * succ (m + k)    : add_succ
       ...              = n * (m + k) + n     : mul_succ
       ...              = (n * m + n * k) + n : mul_distrib
       ...              = n * m + (n * k + n) : add_assoc
       ...              = n * m + n * succ k  : mul_succ

theorem mul_assoc : ∀ n m k : nat, (n * m) * k = n * (m * k)
| mul_assoc n m 0 :=
  calc (n * m) * 0 = 0           : mul_zero
       ...         = n * 0       : mul_zero
       ...         = n * (m * 0) : mul_zero
| mul_assoc n m (succ k) :=
  calc (n * m) * succ k = (n * m) * k + n * m : mul_succ
       ...              = n * (m * k) + n * m : mul_assoc
       ...              = n * (m * k + m)     : mul_distrib
       ...              = n * (m * succ k)    : mul_succ

theorem succ_mul : ∀ n m : nat, succ n * m = n * m + m
| succ_mul n 0 :=
  calc succ n * 0 = 0         : mul_zero
       ...        = 0 + 0     : add_zero
       ...        = n * 0 + 0 : mul_zero
| succ_mul n (succ m) :=
  calc succ n * succ m = succ n * m + succ n  : mul_succ
       ...             = (n * m + m) + succ n : succ_mul
       ...             = n * m + (m + succ n) : add_assoc
       ...             = n * m + succ (m + n) : add_succ
       ...             = n * m + succ (n + m) : add_comm
       ...             = n * m + (n + succ m) : add_succ
       ...             = (n * m + n) + succ m : add_assoc
       ...             = n * succ m + succ m  : mul_succ

theorem mul_comm : ∀ n m : nat, n * m = m * n
| mul_comm n 0 :=
  calc n * 0 = 0     : mul_zero
       ...   = 0 * n : zero_mul
| mul_comm n (succ m) :=
  calc n * succ m = n * m + n  : mul_succ
       ...        = m * n + n  : mul_comm
       ...        = succ m * n : succ_mul

definition pred : nat → nat
| pred 0        := 0
| pred (succ n) := n

theorem pred_succ : ∀ n : nat, pred (succ n) = n
| pred_succ n := rfl

theorem succ_pred : ∀ n : nat, n ≠ 0 → succ (pred n) = n
| succ_pred 0 :=
  assume `0 ≠ 0`,
  absurd rfl `0 ≠ 0`
| succ_pred (succ n) :=
  assume `succ n ≠ 0`, -- 使わない
  calc succ (pred (succ n)) = succ n : pred_succ

definition sub : nat → nat → nat
| sub n 0        := 0
| sub n (succ m) := pred (sub n m)

notation 1 := succ zero

definition pow : nat → nat → nat
| pow n 0        := 1
| pow n (succ m) := pow n m * n

infix `^` := pow

theorem pow_zero : ∀ n : nat, n ^ 0 = 1
| pow_zero n := rfl

theorem pow_succ : ∀ n m : nat, n ^ (succ m) = n ^ m * n
| pow_succ n m := rfl

theorem mul_one : ∀ n : nat, n * 1 = n
| mul_one n :=
  calc n * 1 = n * 0 + n : mul_succ
       ...   = 0 + n     : mul_zero
       ...   = n         : zero_add

theorem pow_add : ∀ n m k : nat, n ^ (m + k) = n ^ m * n ^ k
| pow_add n m 0 :=
  calc n ^ (m + 0) = n ^ m         : add_zero
       ...         = n ^ m * 1     : mul_one
       ...         = n ^ m * n ^ 0 : pow_zero
| pow_add n m (succ k) :=
  calc n ^ (m + succ k) = n ^ succ (m + k)    : add_succ
       ...              = n ^ (m + k) * n     : pow_succ
       ...              = (n ^ m * n ^ k) * n : pow_add
       ...              = n ^ m * (n ^ k * n) : mul_assoc
       ...              = n ^ m * n ^ succ k  : pow_succ

end nat

end sec_6_4

namespace sec_6_5

inductive list (A : Type) : Type :=
| nil {} : list A
| cons   : A → list A → list A

namespace list

variable {A : Type}

notation x :: xs := cons x xs

definition append : list A → list A → list A
| append nil       ys := ys
| append (x :: xs) ys := x :: (append xs ys)

notation xs ++ ys := append xs ys

theorem nil_append : ∀ xs : list A, nil ++ xs = xs
| nil_append xs := rfl

theorem cons_append : ∀ x : A, ∀ xs ys : list A, (x :: xs) ++ ys = x :: (xs ++ ys)
| cons_append x xs ys := rfl

theorem append_nil : ∀ t : list A, t ++ nil = t
| append_nil nil :=
  calc nil ++ nil = nil : nil_append
| append_nil (x :: xs) :=
  calc (x :: xs) ++ nil = x :: (xs ++ nil) : cons_append
       ...              = x :: xs          : append_nil

theorem append_assoc : ∀ xs ys zs : list A, (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
| append_assoc nil ys zs :=
  calc (nil ++ ys) ++ zs = ys ++ zs          : nil_append
       ...               = nil ++ (ys ++ zs) : nil_append
| append_assoc (x :: xs) ys zs :=
  calc ((x :: xs) ++ ys) ++ zs = (x :: (xs ++ ys)) ++ zs : cons_append
       ...                     = x :: ((xs ++ ys) ++ zs) : cons_append
       ...                     = x :: (xs ++ (ys ++ zs)) : append_assoc
       ...                     = (x :: xs) ++ (ys ++ zs) : cons_append

end list

end sec_6_5

namespace sec_6_6

theorem cast {A B : Type} : A = B → A → B := eq.rec_on

theorem subst {A : Type} {a b : A} {P : A → Prop} : a = b → P a → P b :=
  suppose a = b,
  suppose P a,
  eq.rec `P a` `a = b`

theorem symm {A : Type} {a b : A} : a = b → b = a :=
  suppose a = b,
  subst `a = b` (eq.refl a)

theorem trans {A : Type} {a b c : A} : a = b → b = c → a = c :=
  suppose a = b,
  suppose b = c,
  subst `b = c` `a = b`

theorem congr {A B : Type}  {a a' : A} (f : A → B) : a = a' → f a = f a' :=
  suppose a = a',
  subst `a = a'` (eq.refl (f a))

end sec_6_6

namespace sec_6_8

open function

inductive tree (A : Type) : Type :=
| leaf : A → tree A
| node : tree A → tree A → tree A

open tree

variable {A : Type}

theorem leaf_ne_node {a : A} {l r : tree A} : leaf a ≠ node l r :=
  not.intro tree.no_confusion

theorem leaf_inj {a b : A} : leaf a = leaf b → a = b :=
  assume H,
  tree.no_confusion H id

theorem node_inj {l r l' r' : tree A} : node l r = node l' r' → l = l' ∧ r = r' :=
  assume H,
  tree.no_confusion H and.intro

theorem node_inj_left {l r l' r' : tree A} : node l r = node l' r' → l = l' :=
  and.left ∘ node_inj

theorem node_inj_right {l r l' r' : tree A} : node l r = node l' r' → r = r' :=
  and.right ∘ node_inj

end sec_6_8

namespace induction_on_vector

open nat (zero succ)

inductive vector (A : Type) : nat → Type :=
| nil {} : vector A zero
| cons   : Π {n : nat}, A → vector A n → vector A (succ n)

open vector (nil cons)

definition uncons {A : Type} : Π {n : nat}, vector A (succ n) → A × vector A n :=
  have uncons' : Π (m : nat), vector A m → Π n : nat, m = succ n → A × vector A n,
    from take m xxs,
         vector.cases_on xxs
           (take n' H, nat.no_confusion H)
           (take n' x xs n H, pair x (eq.rec xs (nat.succ.inj H))),
  take n xxs, uncons' (succ n) xxs n rfl

open function prod

definition head {A : Type} {n : nat} : vector A (succ n) → A := pr1 ∘ uncons

definition tail {A : Type} {n : nat} : vector A (succ n) → vector A n := pr2 ∘ uncons

definition map {A B : Type} (f : A → B) : Π {n : nat}, vector A n → vector B n :=
  nat.rec (take xs, nil) (take n map_f_n xs, cons (f (head xs)) (map_f_n (tail xs)))

definition zipWith {A B C : Type} (f : A → B → C) : Π {n : nat}, vector A n → vector B n → vector C n :=
  nat.rec (take xs ys, nil) (take n zipWith_f_n xs ys, cons (f (head xs) (head ys)) (zipWith_f_n (tail xs) (tail ys)))

definition zip {A B : Type} {n : nat} : vector A n → vector B n → vector (A × B) n := zipWith pair

end induction_on_vector
