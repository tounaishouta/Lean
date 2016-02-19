import standard

namespace sec7_1

definition sub2 : ℕ → ℕ
| sub2 0       := 0
| sub2 1       := 0
| sub2 (a + 2) := a

eval sub2 0
eval sub2 1
eval sub2 2
eval sub2 3
eval sub2 4
eval sub2 5

inductive bool : Type :=
| ff : bool
| tt : bool

open sec7_1.bool

definition bnot : bool → bool
| bnot ff := tt
| bnot tt := ff

theorem bnot_bnot : ∀ b : bool, bnot (bnot b) = b
| bnot_bnot tt := rfl
| bnot_bnot ff := rfl

inductive nat : Type :=
| zero : nat
| succ : nat → nat

open nat

notation `ℕ` := nat

definition add : ℕ → ℕ → ℕ
| add n zero     := n
| add n (succ m) := succ (n + m)

theorem add_zero (n : ℕ) : n + zero = n := rfl

theorem add_succ (n m : ℕ) : n + succ m = succ (n + m) := rfl

theorem add_assoc : ∀ n m k : ℕ, (n + m) + k = n + (m + k)
| add_assoc n m 0 :=
  calc (n + m) + 0
      = n + m       : add_zero
  ... = n + (m + 0) : {add_zero m}
| add_assoc n m (succ k) :=
  calc (n + m) + succ k
      = succ ((n + m) + k) : add_succ
  ... = succ (n + (m + k)) : add_assoc
  ... = n + succ (m + k)   : add_succ
  ... = n + (m + succ k)   : add_succ

theorem zero_add : ∀ n : ℕ, zero + n = n
| zero_add 0 := rfl
| zero_add (succ n) :=
  calc 0 + succ n
      = succ (0 + n) : add_succ
  ... = succ n       : {zero_add n}

theorem succ_add : ∀ n m : ℕ, succ n + m = succ (n + m)
| succ_add n 0 :=
  calc succ n + 0
     = succ n       : add_zero
  ...= succ (n + 0) : add_zero
| succ_add n (succ m) :=
  calc succ n + succ m
     = succ (succ n + m)   : add_succ
  ...= succ (succ (n + m)) : succ_add
  ...= succ (n + succ m)   : add_succ

theorem add_comm : ∀ n m : ℕ, n + m = m + n
| add_comm n 0 :=
  calc n + 0
     = n     : add_zero
  ...= 0 + n : zero_add
| add_comm n (succ m) :=
  calc n + (succ m)
     = succ (n + m) : add_succ
  ...= succ (m + n) : add_comm
  ...= succ m + n   : succ_add

end sec7_1


namespace sec7_2

end sec7_2

namespace sec7_3

open list

definition map {A B : Type} : (A → B) →  list A → list B
| map f nil      := nil
| map f (h :: t) := f h :: map f t

open nat

eval map succ []
eval map succ [3, 8, 4]

open prod

definition zip {A B : Type} : list A → list B → list (A × B)
| zip nil        _          := nil
| zip _          nil        := nil
| zip (h1 :: t1) (h2 :: t2) := (h1, h2) :: zip t1 t2

eval (zip [3, 8, 4] [2, 9, 7, 5] : list (ℕ × ℕ))
eval (zip [4, 5] [8] : list (ℕ × ℕ))

definition unzip {A B : Type} : list (A × B) → list A × list B
| unzip nil := (nil, nil)
| unzip ((h1, h2) :: t) :=
  match unzip t with
    (t1, t2) := (h1 :: t1, h2 :: t2)
  end

eval (unzip [(4, 7), (6, 8), (5, 2)] : list ℕ × list ℕ)

/-
definition diag {A : Type} : list (list A) → list A
| diag nil             := nil
| diag (nil :: _)      := nil
| diag ((h :: _) :: t) := h :: diag (map tail t)
-/

end sec7_3

namespace sec7_4

open nat

definition f : ℕ → ℕ → ℕ
| f 0 0 := 0
| f 0 _ := 1
| f _ 0 := 2
| f _ _ := arbitrary ℕ

print f
print arbitrary

end sec7_4

namespace sec7_5

end sec7_5
