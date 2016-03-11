import standard

print classes
print instances inhabited

open nat

print default
eval default ℕ
check (rfl : 0 = default ℕ)

print arbitrary
eval arbitrary ℕ
check (rfl : 0 = arbitrary ℕ) --> Error

definition func_is_inhabited [instance]
  {A B : Type} [inhabited B] :
  inhabited (A → B) :=
  inhabited.mk (λ x : A, default B)

definition pi_is_inhabited [instance]
  {A : Type} {C : A → Type} [Π x : A, inhabited (C x)] :
  inhabited (Π x : A, C x) :=
  inhabited.mk (λ x : A, default (C x))

definition sum_is_inhabited_l [instance]
  {A B : Type} [inhabited A] : inhabited (sum A B) :=
  inhabited.mk (sum.inl (default A))

definition sum_is_inhabited_r [instance]
  {A B : Type} [inhabited B] : inhabited (sum A B) :=
  inhabited.mk (sum.inr (default B))

eval default (sum nat nat)
eval default (sum nat empty)
eval default (sum empty nat)

namespace my_has_add

inductive has_add [class] (A : Type) : Type :=
| mk : (A → A → A) → has_add A

definition add {A : Type} [H : has_add A] : A → A → A :=
  has_add.rec id H

infix + := add

definition bool_has_add [instance] : has_add bool :=
  has_add.mk bool.bxor

definition nat_has_add [instance] : has_add nat :=
  has_add.mk nat.add

private definition add_prod {A B : Type} [has_add A] [has_add B]
: A × B → A × B → A × B
| add_prod (a1, b1) (a2, b2) := (a1 + a2, b1 + b2)

definition prod_has_add [instance] {A B : Type} [has_add A] [has_add B]
: has_add (A × B)
| prod_has_add := has_add.mk add_prod

eval ((1, 2) + (3, 4) : nat × nat)

private definition add_fun {A B : Type} [has_add B]
: (A → B) → (A → B) → (A → B)
| add_fun f g a := f a + g a

definition fun_has_add [instance] {A B : Type} [has_add B]
: has_add (A → B)
| fun_has_add := has_add.mk add_fun

eval ((λ n : ℕ, n + 1) + (λ n : ℕ, 2 * n)) 3

open list

private definition add_list {A : Type} [has_add A]
 : list A → list A → list A
 | add_list nil       _         := nil
 | add_list _         nil       := nil
 | add_list (x :: xs) (y :: ys) := (x + y) :: add_list xs ys

definition list_has_add [instance] {A : Type} [has_add A]
: has_add (list A)
| list_has_add := has_add.mk add_list

eval ([1, 2, 3] + [4, 5, 6] : list nat)

namespace vector

inductive vector (A : Type) : ℕ → Type :=
| nil {} : vector A 0
| cons   : Π {n : ℕ}, A  → vector A n → vector A (succ n)

open vector

notation x `::` xs := cons x xs

private definition add_vector {A : Type} [has_add A]
: Π {n : ℕ}, vector A n → vector A n → vector A n
| add_vector nil nil             := nil
| add_vector (x :: xs) (y :: ys) := (x + y) :: add_vector xs ys

definition vector_has_add [instance] {A : Type} [has_add A] {n : ℕ}
: has_add (vector A n)
| vector_has_add := has_add.mk add_vector

eval (1 :: 2 :: 3 :: nil + 4 :: 5 :: 6 :: nil : vector ℕ 3)

end vector

end my_has_add
