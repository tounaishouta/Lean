import standard

print "\n Pi type in Lean \n"

namespace hide1

constant A : Type
constant B : A → Type

check Π (x : A), B x -- backslash P
check Π x : A, B x -- same as above
check Pi x : A, B x -- same as above

constant C : A → A → Type

check Π x : A, Π y : A, C x y
check Π (x : A) (y : A), C x y -- same as above
check Π (x y : A), C x y -- same as above
check Π x y : A, C x y -- same as above

constant D : Type

check A → D
check Π x : A, D -- same as above

end hide1

print "\n Let's define `identity` \n"

constant n : ℕ
constant b : bool

print "\n 1. それぞれ作る \n"

definition id_nat (n : ℕ) : ℕ := n
check id_nat
eval id_nat n

definition id_bool (b : bool) : bool := b
check id_bool
eval id_bool b

-- 全部するのは面倒だし無駄 DRY

print "\n 2. Use Pi type \n"

definition id1 (X : Type) (x : X) : X := x
/-
definition id1
: Π X : Type, X → X
:= λ (X : Type) (x : X), x
-/
check id1

eval id1 ℕ n

eval id1 bool b

print "\n 3. Use underscore _ \n"

check id1 _ n
eval id1 _ n
eval id1 _ b

print "\n 4. Use curly brace { } \n"

definition id2 {X : Type} (x : X) : X := x
/-
definition id2
: Π {X : Type}, X → X
:= λ (X : Type) (x : X), x
-/

check id2
eval id2 n
eval id2 b

print "\n use @ \n"

check @id2 -- @ を使うと implicit が explicit に
eval @id2 ℕ n
eval @id2 bool b

print "\n use ! \n"

check !id1 -- ! はその逆
eval !id1 n
eval !id1 b

print "\n Let's define `composition` \n"

definition comp {A B C : Type} (g : B → C) (f : A → B) (x : A) : C := g (f x)
check comp
check @comp
eval comp (λ x : ℕ, x + 5) (λ x : ℕ, x + 7) 8

definition do_twice {A : Type} (f : A → A) := comp f f
check do_twice
check @do_twice
eval do_twice (λ x : ℕ, x + 3) 5

print "\n library の list についてみてみよう \n"

open list

check list
check nil
check @nil
check cons
check @cons
check head
check @head
check tail
check @tail
check append
check @append

print "\n 上を参考に vec について考えてみよう \n"
-- vec A n は A の元を n 個並べたものの型
-- 数学における A^n
namespace hide2

constant vec : Type → ℕ → Type

namespace vec
constant nil : Π {X : Type}, vec X 0
constant cons : Π {X : Type} {n : ℕ}, X → vec X n → vec X (n + 1)
constant append : Π {X : Type} {n m : ℕ}, vec X n → vec X m → vec X (n + m)

open bool

constant v1 : vec bool 10
constant v2 : vec bool 20
check cons tt nil
check cons ff v1
check append v1 v2

end vec
end hide2

print "\n Sigma type in Lean \n"

namespace hide3
open sigma

constant A : Type
constant B : A → Type
constant C : Type
constant a : A
constant b : B a

check sigma
check @sigma

check sigma B
check Σ x : A, B x -- same as above (backslash S)

check sigma.mk
check @sigma.mk

check sigma.mk a b
check ⟨a, b⟩ -- smae as above  (backslash less, backslash greater)

check A × C
check Σ x : A, C -- same as above <- wrong

check pr1 -- pr₁ でも OK (pr backslash undersocre 1)
check @pr1
check pr2 -- pr₂ でも OK
check @pr2

check pr1 ⟨a, b⟩
check pr2 ⟨a, b⟩
eval pr1 ⟨a, b⟩
eval pr2 ⟨a, b⟩

end hide3

print "\n Prop in Lean \n"

check Prop
check Type.{0}

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
