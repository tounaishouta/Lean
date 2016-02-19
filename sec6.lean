import standard

namespace sec6_1

-- inductive type の作り方
inductive weekday : Type :=
  | sunday    : weekday
  | monday    : weekday
  | tuesday   : weekday
  | wednesday : weekday
  | thursday  : weekday
  | friday    : weekday
  | saturday  : weekday

-- constructor と recursor は namespace weekday の中に
print prefix sec6_1.weekday

open weekday

-- recursor の使い方
definition next_day : weekday → weekday :=
  weekday.rec monday tuesday wednesday thursday friday saturday sunday

-- 応用例

definition const {A B : Type} : A → B → A :=
  λ a b, a

definition comp {A B C : Type} : (A → B) → (B → C) → (A → C) :=
  λ f g x, g (f x)

definition iterate {A : Type} : ℕ → (A → A) → (A → A) :=
  nat.rec (const id) (λ n G f, comp (G f) f)
  
definition day_after (n : ℕ) : weekday → weekday :=
  iterate n next_day

eval day_after 3 monday

end sec6_1

--------------------------------------------------------------------------------

namespace sec6_2

-- 引数をとる inductive type
inductive prod (A B : Type) :=
| mk {} : A → B → prod A B

infix `*` := prod
notation `(` x `,` y `)` := prod.mk x y

print prod
print prod.mk
print prod.rec
print prod.rec_on

check prod.rec
check @prod.rec

definition pr1 {A B : Type} : prod A B → A := prod.rec (λ a b, a)

definition pr2 {A B : Type} : prod A B → B := prod.rec (λ a b, b)

print pr1
print pr2

open bool nat

print cond

definition ex_prod : bool * ℕ → ℕ :=
  prod.rec (bool.rec (λ n, 2 * n) (λ n, 2 * n + 1))

eval ex_prod (ff, 3)
eval ex_prod (tt, 3)

inductive sum (A B : Type) :=
| inl {} : A → sum A B
| inr {} : B → sum A B

infix `+` := sum

print sum
print sum.inl
print sum.inr
print sum.rec

definition ex_sum : ℕ + ℕ → ℕ :=
  sum.rec (λ n, 2 * n) (λ n, 2 * n + 1)

eval ex_sum (sum.inl 3)
eval ex_sum (sum.inr 3)

structure Semigroup : Type :=
  (carrier : Type)
  (mul : carrier → carrier → carrier)
  (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))

definition NatAdd : Semigroup :=
  Semigroup.mk ℕ add nat.add_assoc

-- eval Semigroup.mul NatAdd (7 : ℕ) (8 : ℕ)

-- As exercises, we encourage you to develop a notion of composition for partial functions from A to B and B to C, and show that it behaves as expected. We also encourage you to show that bool and nat are inhabited, that the product of two inhabited types is inhabited, and that the type of functions to an inhabited type is inhabited.

end sec6_2

--------------------------------------------------------------------------------

namespace sec6_3

print notation ∧
print and

print notation ∨
print or

print false

-- ∃ a : A, P === Exists (λ a : A, P)
print Exists

-- { a : A | P } === subtype (λ a : A, P)
print subtype

end sec6_3

--------------------------------------------------------------------------------

-- Defining the Natural Number
namespace sec6_4

open nat

print nat

print add

theorem add_zero : ∀ a : ℕ, a + 0 = a := take a, rfl

theorem add_succ : ∀ a b : ℕ, a + succ b = succ (a + b) := take a b, rfl

theorem add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c) :=
take a b,
nat.rec (
  calc
    (a + b) + 0 = a + b       : add_zero
    ...         = a + (b + 0) : add_zero
) (
  take c,
  assume H : (a + b) + c = a + (b + c),
  calc
    (a + b) + succ c = succ ((a + b) + c) : add_succ
    ...              = succ (a + (b + c)) : H
    ...              = a + succ (b + c)   : add_succ
    ...              = a + (b + succ c)   : add_succ
)

theorem zero_add : ∀ a : ℕ, 0 + a = a :=
nat.rec (
  calc 0 + 0 = 0 : add_zero
) (
  take a,
  assume H : 0 + a = a,
  calc 0 + succ a = succ (0 + a) : add_succ
              ... = succ a       : H
)

theorem succ_add : ∀ a b : ℕ, succ a + b = succ (a + b) :=
take a,
nat.rec (
  calc succ a + 0 = succ a       : add_zero
              ... = succ (a + 0) : add_zero
) (
  take b,
  assume H : succ a + b = succ (a + b),
  calc succ a + succ b = succ (succ a + b)   : add_succ
                   ... = succ (succ (a + b)) : H
                   ... = succ (a + succ b)   : add_succ
                   ... = a + succ (succ b)   : add_succ
)

theorem add_comm : ∀ a b : ℕ, a + b = b + a :=
take a,
nat.rec (
  calc
    a + 0 = a     : add_zero
    ...   = 0 + a : zero_add
) (
  take b,
  assume H : a + b = b + a,
  calc a + succ b = succ (a + b) : add_succ
              ... = succ (b + a) : H
              ... = succ b + a   : succ_add
)

definition pred : ℕ → ℕ :=
nat.rec 0 (λ a b, a)

eval pred 0
eval pred 1
eval pred 2
eval pred 3

theorem pred_succ : ∀ a : ℕ, pred (succ a) = a := take a, rfl

theorem succ_pred : ∀ a : ℕ, a ≠ 0 → succ (pred a) = a :=
nat.rec (
  assume H : 0 ≠ 0,
  absurd rfl H
) (
  take a,
  assume H1,
  assume H2,
  pred_succ (succ a)
)

end sec6_4

namespace sec6_4'

open nat

definition factorial : ℕ → ℕ :=
nat.rec 1 (λ n f, (n + 1) * f)

eval factorial 7

print nat.no_confusion
print nat.no_confusion_type
eval nat.no_confusion_type bool zero (succ zero)

end sec6_4'
--------------------------------------------------------------------------------

namespace sec6_5

end sec6_5

--------------------------------------------------------------------------------

namespace sec6_6

open nat

namespace foo

inductive Vector : Type → ℕ → Type :=
| nil  : Π {A : Type}, Vector A zero
| cons : Π {A : Type} {n : ℕ}, A → Vector A n → Vector A (succ n)

check @Vector.rec

end foo

namespace bar -- こっちが好ましい

inductive Vector (A : Type) : ℕ → Type :=
| nil  : Vector A zero
| cons : Π {n : ℕ}, A → Vector A n → Vector A (succ n)

check @Vector.rec

end bar

end sec6_6

--------------------------------------------------------------------------------

namespace sec6_7

end sec6_7

--------------------------------------------------------------------------------

namespace sec6_8

open nat

print nat.no_confusion
print nat.no_confusion_type

example : ∀ a : ℕ, 0 ≠ succ a := 
take a,
not.intro (
  assume H : 0 = succ a,
  nat.no_confusion H
)

example : ∀ a b : ℕ, succ a = succ b → a = b :=
take a b,
assume H : succ a = succ b,
show a = b,
from nat.no_confusion H id

open sigma

print notation ==
print heq
print heq.rec

example (A : Type) (B : A → Type) (a a' : A) (f : Π (x : A), B x) (H : a == a') : f a == f a' := sorry

end sec6_8
