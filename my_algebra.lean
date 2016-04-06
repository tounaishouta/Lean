import standard

namespace my_algebra

/- Magma -/
section

  structure Magma.{l} : Type.{l + 1} :=
    (carrier : Type.{l})
    (mul : carrier → carrier → carrier)

end

/- Semigroup -/
section

  structure Semigroup.{l} extends Magma.{l} : Type.{l + 1} :=
    (mul_assoc : ∀ {x y z : carrier}, mul x (mul y z) = mul (mul x y) z)

  local attribute Magma.carrier [coercion]
  local infix ` * ` := Semigroup.mul _

  section
    variables {S : Semigroup} {x y z : S}
    example : x * (y * z) = (x * y) * z := Semigroup.mul_assoc S
  end

end

/- uMagma -/
section

  structure uMagma.{l} extends Magma.{l} : Type.{l + 1} :=
    (unit : carrier)
    (unit_mul : ∀ {x : carrier}, mul unit x = x)
    (mul_unit : ∀ {x : carrier}, mul x unit = x)

  local attribute uMagma.carrier [coercion]
  local infix ` * ` := uMagma.mul _
  local notation 1 := uMagma.unit _

  section
    variables {U : uMagma} {x : U}
    example : 1 * x = x := uMagma.unit_mul U
    example : x * 1 = x := uMagma.mul_unit U
  end

end

/- Monoid -/
section

  structure Monoid.{l} extends Semigroup.{l}, uMagma.{l} : Type.{l + 1} :=
    mk ::

  local attribute Monoid.carrier [coercion]
  local infix ` * ` := Monoid.mul _
  local notation 1 := Monoid.unit _

  section
    variables {M : Monoid} {x y z : M}
    example : x * (y * z) = (x * y) * z := Monoid.mul_assoc M
    example : 1 * x = x := Monoid.unit_mul M
    example : x * 1 = x := Monoid.mul_unit M
  end

  open [notation] list
  open list (map)

  definition product {M : Monoid} : list M → M :=
    list.rec 1 (take hd tl prod_tl, hd * prod_tl)

  theorem product_append {M : Monoid} {xs ys : list M}
  : product (xs ++ ys) = product xs * product ys :=
  list.rec_on xs
    (calc
      product ([] ++ ys)
      = product ys : rfl ...
      = 1 * product ys : Monoid.unit_mul ...
      = product [] * product ys : rfl)
    (take x xs' IH, calc
      product ((x :: xs') ++ ys)
      = product (x :: (xs' ++ ys)) : rfl ...
      = x * product (xs' ++ ys) : rfl ...
      = x * (product xs' * product ys) : IH ...
      = (x * product xs') * product ys : Monoid.mul_assoc ...
      = product (x :: xs') * product ys : rfl)

  definition join {T : Type} : list (list T) → list T :=
    list.rec [] (take hd tl con_tl, hd ++ con_tl)

  theorem product_join {M : Monoid} {xss : list (list M)}
  : product (join xss) = product (map product xss) :=
  list.rec_on xss
    rfl
    (take xs xss' IH, calc
      product (join (xs :: xss'))
      = product (xs ++ join xss') : rfl ...
      = product xs * product (join xss') : product_append ...
      = product xs * product (map product xss') : IH ...
      = product (product xs :: map product xss') : rfl ...
      = product (map product (xs :: xss')) : rfl)

  theorem product_pure  {M : Monoid} {x : M}
  : product [x] = x := calc
    product [x]
    = x * 1 : rfl ...
    = x : Monoid.mul_unit

end

/- Monoid from list operator -/
section
  
  open [notation] list
  open list (map)

  definition Monoid.from_prod
    (T : Type)
    (prod : list T → T)
    (prod_join : ∀ {xss : list (list T)}, prod (join xss) = prod (map prod xss))
    (prod_pure : ∀ {x : T}, prod [x] = x)
    : Monoid :=
    ⦃ Monoid,
      carrier := T,
      mul := take x y, prod [x, y],
      unit := prod [],
      mul_assoc := take x y z, calc
        prod [x, prod [y, z]]
        = prod [prod [x], prod [y, z]] : prod_pure ...
        = prod (map prod [[x], [y, z]]) : rfl ...
        = prod (join [[x], [y, z]]) : prod_join ...
        = prod [x, y, z] : rfl ...
        = prod (join [[x, y], [z]]) : rfl ...
        = prod (map prod [[x, y], [z]]) : prod_join ...
        = prod [prod [x, y], prod [z]] : rfl ...
        = prod [prod [x, y], z] : prod_pure,
      unit_mul := take x, calc
        prod [prod [], x]
        = prod [prod [], prod [x]] : prod_pure ...
        = prod (map prod [[], [x]]) : rfl ...
        = prod (join [[], [x]]) : prod_join ...
        = prod [x] : rfl ...
        = x : prod_pure,
      mul_unit := take x, calc
        prod [x, prod[]]
        = prod [prod [x], prod []] : prod_pure ...
        = prod (map prod [[x], []]) : rfl ...
        = prod (join [[x], []]) : prod_join ...
        = prod [x] : rfl ...
        = x : prod_pure ⦄

end

/- Group -/
section

  structure Group.{l} extends Monoid.{l} : Type.{l + 1} :=
    (inv : carrier → carrier)
    (inv_mul : ∀ {x : carrier}, mul (inv x) x = unit)
    (mul_inv : ∀ {x : carrier}, mul x (inv x) = unit)

  local attribute Group.carrier [coercion]
  local infix ` * ` := Group.mul _
  local notation 1 := Group.unit _
  local notation x `⁻¹` := Group.inv _ x

  section
    variables {G : Group} {x y z : G}
    example : x * (y * z) = (x * y) * z := Group.mul_assoc G
    example : 1 * x = x := Group.unit_mul G
    example : x * 1 = x := Group.mul_unit G
    example : x⁻¹ * x = 1 := Group.inv_mul G
    example : x * x⁻¹ = 1 := Group.mul_inv G
  end

end

/- subgroup of invertible elements of monoid -/
section

  local attribute Monoid.carrier [coercion]
  local infix ` * ` := Monoid.mul _
  local notation 1 := Monoid.unit _

  structure inv_pair (M : Monoid) :=
    (self : M)
    (inv : M)
    (inv_mul : inv * self = 1)
    (mul_inv : self * inv = 1)

  theorem inv_pair.eq {M : Monoid} {x y : inv_pair M}
    : inv_pair.self x = inv_pair.self y → inv_pair.inv x = inv_pair.inv y → x = y :=
    begin
      cases x,
      cases y,
      esimp,
      intro H H',
      congruence,
      { exact H },
      { exact H' }
    end

  local attribute inv_pair.self [coercion]
  local notation x `⁻¹` := inv_pair.inv x

  definition inv_subgroup (M : Monoid) : Group :=
    ⦃ Group,
      carrier := inv_pair M,
      mul := take x y,
        ⦃ inv_pair M,
          self := x * y,
          inv := y⁻¹ * x⁻¹,
          inv_mul := calc
            (y⁻¹ * x⁻¹) * (x * y)
            = y⁻¹ * (x⁻¹ * x) * y : by rewrite +Monoid.mul_assoc ...
            = y⁻¹ * 1 * y : by rewrite inv_pair.inv_mul ...
            = y⁻¹ * y : by rewrite Monoid.mul_unit ...
            = 1 : by rewrite inv_pair.inv_mul,
          mul_inv := calc
            (x * y) * (y⁻¹ * x⁻¹)
            = x * (y * y⁻¹) * x⁻¹ : by rewrite +Monoid.mul_assoc ...
            = x * 1 * x⁻¹ : by rewrite inv_pair.mul_inv ...
            = x * x⁻¹ : by rewrite Monoid.mul_unit ...
            = 1 : by rewrite inv_pair.mul_inv ⦄,
      unit :=
        ⦃ inv_pair M,
          self := 1,
          inv := 1,
          inv_mul := Monoid.mul_unit M,
          mul_inv := Monoid.mul_unit M ⦄,
      inv := take x,
        ⦃ inv_pair M,
          self := x⁻¹,
          inv := x,
          inv_mul := inv_pair.mul_inv x,
          mul_inv := inv_pair.inv_mul x ⦄,
      mul_assoc := take x y z, inv_pair.eq
        (by rewrite [▸*, Monoid.mul_assoc])
        (by rewrite [▸*, Monoid.mul_assoc]),
      unit_mul := take x, inv_pair.eq
        (by rewrite [▸*, Monoid.unit_mul])
        (by rewrite [▸*, Monoid.mul_unit]),
      mul_unit := take x, inv_pair.eq
        (by rewrite [▸*, Monoid.mul_unit])
        (by rewrite [▸*, Monoid.unit_mul]),
      inv_mul := take x, inv_pair.eq
        (by rewrite [▸*, inv_pair.inv_mul])
        (by rewrite [▸*, inv_pair.inv_mul]),
      mul_inv := take x, inv_pair.eq
        (by rewrite [▸*, inv_pair.mul_inv])
        (by rewrite [▸*, inv_pair.mul_inv]) ⦄
  
  definition End (T : Type) : Monoid :=
    ⦃ Monoid,
      carrier := T → T,
      mul := function.comp,
      unit := id,
      mul_assoc := take x y z, rfl,
      unit_mul := take x, rfl,
      mul_unit := take x, rfl ⦄

  definition Aut (T : Type) : Group := inv_subgroup (End T)

end

end my_algebra
