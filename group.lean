import standard

--set_option pp.all true

namespace binary

structure Magma :=
  (carrier : Type₁)
  (mul : carrier → carrier → carrier)

attribute Magma.carrier [coercion]

infix ` * ` := Magma.mul _

structure Semigroup extends Magma :=
  (mul_assoc : ∀ {x y z : carrier}, mul x (mul y z) = mul (mul x y) z)

example (S : Semigroup) (x y z : S) : x * (y * z) = (x * y) * z :=
  Semigroup.mul_assoc S

structure UMagma extends Magma :=
  (unit : carrier)
  (unit_mul : ∀ {x : carrier}, mul unit x = x)
  (mul_unit : ∀ {x : carrier}, mul x unit = x)

notation 1 := UMagma.unit _

example (M : UMagma) (x : M) : 1 * x = x := UMagma.unit_mul M
example (M : UMagma) (x : M) : x * 1 = x := UMagma.mul_unit M

structure Monoid extends Semigroup, UMagma :=
  mk ::

theorem Monoid.mul_assoc' {M : Monoid} {x y z : M}
  : x * (y * z) = (x * y) * z := Monoid.mul_assoc M
theorem Monoid.unit_mul' {M : Monoid} {x : M} : 1 * x = x := Monoid.unit_mul M
theorem Monoid.mul_unit' {M : Monoid} {x : M} : x * 1 = x := Monoid.mul_unit M

structure Group extends Monoid :=
  (inv : carrier → carrier)
  (mul_self_inv : ∀ {x : carrier}, mul x (inv x) = unit)
  (mul_inv_self : ∀ {x : carrier}, mul (inv x) x = unit)

notation x `⁻¹` := Group.inv _ x

example (G : Group) (x y z : G) : x * (y * z) = (x * y) * z := Group.mul_assoc G
example (G : Group) (x : G) : 1 * x = x := Group.unit_mul G
example (G : Group) (x : G) : x * 1 = x := Group.mul_unit G
example (G : Group) (x : G) : x⁻¹ * x = 1 := Group.mul_inv_self G
example (G : Group) (x : G) : x * x⁻¹ = 1 := Group.mul_self_inv G

example (G : Group) (x y : G) : Group.mul G x y = Magma.mul G x y := rfl

definition NatAdd : Monoid :=
  ⦃ Monoid,
    carrier := nat,
    mul := nat.add,
    mul_assoc := take x y z, eq.symm (nat.add_assoc x y z),
    unit := nat.zero,
    unit_mul := nat.zero_add,
    mul_unit := nat.add_zero ⦄

definition NatMul : Monoid :=
  ⦃ Monoid,
    carrier := nat,
    mul := nat.mul,
    mul_assoc := take x y z, eq.symm (nat.mul_assoc x y z),
    unit := nat.succ nat.zero,
    unit_mul := nat.one_mul,
    mul_unit := nat.mul_one ⦄

definition End (A : Type₁) : Monoid :=
  ⦃ Monoid,
    carrier := A → A,
    mul := function.comp,
    mul_assoc := take h g f, rfl,
    unit := id,
    unit_mul := take f, rfl,
    mul_unit := take f, rfl ⦄

structure inv_pair (M : Monoid) :=
  (self : M)
  (inv : M)
  (mul_self_inv : self * inv = 1)
  (mul_inv_self : inv * self = 1)

theorem inv_pair.eq {M : Monoid} {x y : inv_pair M}
  (H : inv_pair.self x = inv_pair.self y) (H' : inv_pair.inv x = inv_pair.inv y)
  : x = y :=
  begin
    cases x,
    cases y,
    congruence,
    { exact H },
    { exact H' }
  end

definition InvSub (M : Monoid) : Group :=
  ⦃ Group,
    carrier := inv_pair M,
    mul := take x y,
      ⦃ inv_pair M,
        self := inv_pair.self x * inv_pair.self y,
        inv := inv_pair.inv y * inv_pair.inv x,
        mul_self_inv := calc
          (inv_pair.self x * inv_pair.self y) * (inv_pair.inv y * inv_pair.inv x)
          = inv_pair.self x * (inv_pair.self y * inv_pair.inv y) * inv_pair.inv x
            : by rewrite +Monoid.mul_assoc' ...
          = inv_pair.self x * inv_pair.inv x
            : by rewrite [inv_pair.mul_self_inv, Monoid.mul_unit'] ...
          = 1
            : inv_pair.mul_self_inv,
        mul_inv_self := calc
          (inv_pair.inv y * inv_pair.inv x) * (inv_pair.self x * inv_pair.self y)
          = inv_pair.inv y * (inv_pair.inv x * inv_pair.self x) * inv_pair.self y
            : by rewrite +Monoid.mul_assoc' ...
          = inv_pair.inv y * inv_pair.self y
            : by rewrite [inv_pair.mul_inv_self, +Monoid.mul_unit'] ...
          = 1
            : inv_pair.mul_inv_self ⦄,
    mul_assoc := take x y z,
      begin
        apply inv_pair.eq,
        { rewrite [▸*, Monoid.mul_assoc'] },
        { rewrite [▸*, Monoid.mul_assoc'] }
      end,
    unit :=
      ⦃ inv_pair M,
        self := 1,
        inv := 1,
        mul_self_inv := Monoid.unit_mul',
        mul_inv_self := Monoid.unit_mul' ⦄,
    unit_mul := take x,
      begin
        apply inv_pair.eq,
        { rewrite [▸*, Monoid.unit_mul'] },
        { rewrite [▸*, Monoid.mul_unit'] }
      end,
    mul_unit := take x,
      begin
        apply inv_pair.eq,
        { rewrite [▸*, Monoid.mul_unit'] },
        { rewrite [▸*, Monoid.unit_mul'] }
      end,
    inv := take x,
      ⦃ inv_pair M,
        self := inv_pair.inv x,
        inv := inv_pair.self x,
        mul_self_inv := inv_pair.mul_inv_self x,
        mul_inv_self := inv_pair.mul_self_inv x ⦄,
    mul_self_inv := take x,
      begin
        apply inv_pair.eq,
        { rewrite [▸*, inv_pair.mul_self_inv] },
        { rewrite [▸*, inv_pair.mul_self_inv] }
      end,
    mul_inv_self := take x,
      begin
        apply inv_pair.eq,
        { rewrite [▸*, inv_pair.mul_inv_self] },
        { rewrite [▸*, inv_pair.mul_inv_self] }
      end ⦄

definition Aut (A : Type₁) : Group := InvSub (End A)

end binary
