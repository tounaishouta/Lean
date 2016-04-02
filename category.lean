import standard

namespace category

structure Category : Type :=
  (Ob : Type)
  (Hom : Ob → Ob → Type)
  (comp : Π {x y z : Ob}, Hom y z → Hom x y → Hom x z)
  (id : Π x : Ob, Hom x x)
  (comp_assoc : ∀ {x y z w : Ob} {f : Hom x y} {g : Hom y z} {h : Hom z w},
    comp (comp h g) f = comp h (comp g f))
  (comp_id : ∀ {x y : Ob} {f : Hom x y}, comp f (id x) = f)
  (id_comp : ∀ {x y : Ob} {f : Hom x y}, comp (id y) f = f)

attribute Category.Ob [coercion]
-- attribute Category.Hom [coercion] -- 上手くいかない
open Category (Hom)
infixr ` ∘ ` := Category.comp _
notation 1 := Category.id _ _

definition op [reducible] (C : Category) : Category :=
  ⦃ Category,
    Ob := C,
    Hom := take x y, Hom C y x,
    comp := take x y z g f, Category.comp C f g,
    id := take x, Category.id C x,
    comp_assoc := take x y z w f g h, eq.symm (Category.comp_assoc C),
    comp_id := take x y f, Category.id_comp C,
    id_comp := take x y f, Category.comp_id C ⦄

prefix `-` := op

open prod (pr1 pr2)

definition prod [reducible] (C D : Category) : Category :=
  ⦃ Category,
    Ob := C × D,
    Hom := take x y, Hom C (pr1 x) (pr1 y) × Hom D (pr2 x) (pr2 y),
    comp := take x y z g f, (pr1 g ∘ pr1 f, pr2 g ∘ pr2 f),
    id := take x, (1, 1),
    comp_assoc := take x y z w h g f, prod.eq
      (Category.comp_assoc C)
      (Category.comp_assoc D),
    comp_id := take x y f, prod.eq
      (Category.comp_id C)
      (Category.comp_id D),
    id_comp := take x y f, prod.eq
      (Category.id_comp C)
      (Category.id_comp D) ⦄

infix ` × ` := prod

definition Type_ [reducible] : Category :=
  ⦃ Category,
    Ob := Type,
    Hom := take x y, x → y,
    comp := take x y z g f a, g (f a),
    id := take x a, a,
    comp_assoc := take x y z w f g h, rfl,
    comp_id := take x y f, rfl,
    id_comp := take x y f, rfl ⦄

structure Functor (C D : Category) : Type :=
  (ob : C → D)
  (hom : Π {x y : C}, Hom C x y → Hom D (ob x) (ob y))
  (resp_comp : ∀ {x y z : C} {f : Hom C x y} {g : Hom C y z},
    hom (g ∘ f) = hom g ∘ hom f)
  (resp_id : ∀ {x : C}, hom (1 : Hom C x x) = (1 : Hom D (ob x) (ob x)))

attribute Functor.ob [coercion]
attribute Functor.hom [coercion]

definition HomFunc [reducible] (C : Category) : Functor (-C × C) Type_ :=
  ⦃ Functor (-C × C) Type_,
    ob := take x, Hom C (pr1 x) (pr2 x),
    hom := take x y f a, pr2 f ∘ a ∘ pr1 f,
    resp_comp := take x y z f g, funext (take a,
      by unfold [op, prod, Type_]; rewrite +Category.comp_assoc),
    resp_id := take x, funext (take a,
      by unfold [op, prod, Type_];
         rewrite [Category.comp_id, Category.id_comp]) ⦄

definition Cat [reducible] : Category :=
  ⦃ Category,
    Ob := Category,
    Hom := Functor,
    comp := take C D E G F,
      proof
        ⦃ Functor C E,
          ob := take x, G (F x),
          hom := take x y f, G (F f),
          resp_comp := take x y z g f, by rewrite 2 Functor.resp_comp,
          resp_id := take x, by rewrite 2 Functor.resp_id ⦄
      qed,
    id := take C,
      proof
        ⦃ Functor C C,
          ob := take x, x,
          hom := take x y f, f,
          resp_comp := take x y z g f, rfl,
          resp_id := take x, rfl ⦄
      qed,
    comp_assoc := take A B C D F G H, rfl,
    comp_id := take C D F, by cases F; reflexivity,
    id_comp := take C D F, by cases F; reflexivity ⦄

structure NatTrans {C D : Category} (F G : Functor C D) : Type :=
  (trans : Π x : C, Hom D (F x) (G x))
  (comm : ∀ (x y : C) (f : Hom C x y), G f ∘ trans x = trans y ∘ F f)

attribute NatTrans.trans [coercion]

theorem NatTrans.eq {C D : Category} {F G : Functor C D} {ξ η : NatTrans F G}
  : (∀ x : C, ξ x = η x) → ξ = η :=
  begin
    cases ξ,
    cases η,
    intro H,
    congruence,
    apply funext,
    exact H
  end

definition Func (C D : Category) : Category :=
  ⦃ Category,
    Ob := Functor C D,
    Hom := NatTrans,
    comp := take F G H η ξ,
      proof
        ⦃ NatTrans F H,
          trans := take x, η x ∘ ξ x,
          comm := take x y f,
            by rewrite [ -Category.comp_assoc,
                         NatTrans.comm,
                         Category.comp_assoc,
                         NatTrans.comm,
                         -Category.comp_assoc ] ⦄
      qed,
    id := take F,
      proof
        ⦃ NatTrans F F,
          trans := take x, 1,
          comm := take x y f,
            by rewrite [Category.comp_id, Category.id_comp] ⦄
      qed,
    comp_assoc := take F G H K ξ η ζ, NatTrans.eq (take x,
      by rewrite [▸*, Category.comp_assoc]),
    comp_id := take F G ξ, NatTrans.eq (take x,
      by rewrite [▸*, Category.comp_id]),
    id_comp := take F G ξ, NatTrans.eq (take x,
      by rewrite [▸*, Category.id_comp]) ⦄

definition adj_ob [reducible] {C D E : Category} (F : Functor (C × D) E)
  (x' : D) : Functor C E :=
  ⦃ Functor C E,
    ob := take x, F (x, x'),
    hom := take x y f, F (f, 1),
    resp_comp := take x y z f g,
      by rewrite [-Functor.resp_comp, ↑prod, Category.comp_id],
    resp_id := take x,
      by rewrite -Functor.resp_id ⦄

definition adj_hom [reducible] {C D E : Category} (F : Functor (C × D) E)
  {x' y' : D} (f' : Hom D x' y') : NatTrans (adj_ob F x') (adj_ob F y') :=
  ⦃ NatTrans (adj_ob F x') (adj_ob F y'),
    trans := take x, F (1, f'),
    comm := take x y f,
      begin
        unfold adj_ob,
        rewrite -2 Functor.resp_comp,
        unfold prod,
        rewrite [2 Category.comp_id, 2 Category.id_comp]
      end
  ⦄

definition adj [reducible] {C D E : Category} (F : Functor (C × D) E)
  : Functor D (Func C E) :=
  ⦃ Functor D (Func C E),
    ob := adj_ob F,
    hom := @(adj_hom F),
    resp_comp := take x' y' z' f' g', NatTrans.eq (take x,
      begin
        unfold [adj_hom, Func],
        rewrite -Functor.resp_comp,
        unfold prod,
        rewrite Category.comp_id
      end),
    resp_id := take x', NatTrans.eq (take x,
      begin
        unfold [adj_hom, Func],
        rewrite -Functor.resp_id
      end) ⦄

definition Yoneda [reducible] (C : Category) : Functor C (Func (-C) Type_)
  := adj (HomFunc C)

definition Y_ob [reducible] (C : Category) (x : C) : Functor (-C) Type_
  := Yoneda C x

definition Y_hom [reducible] (C : Category) {x y : C} (f : Hom C x y)
  : NatTrans (Y_ob C x) (Y_ob C y) := Yoneda C f

theorem Y_ob_ob {C : Category} {a x : C} : Y_ob C x a = Hom C a x := rfl

theorem Y_ob_hom {C : Category} {a b x : C} {f : Hom C a b} {g : Hom C b x}
  : Y_ob C x f g = g ∘ f :=
  begin
    unfold [Y_ob, Yoneda, adj, adj_ob, HomFunc],
    rewrite Category.id_comp
  end

theorem Y_hom_ob {C : Category} {a x y : C} {f : Hom C a x} {g : Hom C x y}
  : Y_hom C g a f = g ∘ f :=
  begin
    unfold [Y_hom, Yoneda, adj, adj_hom, HomFunc, op],
    rewrite Category.comp_id
  end

definition bijective {X Y : Type} (f : X → Y) : Prop :=
  ∃ g : Y → X, (∀ x : X, g (f x) = x) ∧ (∀ y : Y, f (g y) = y)

definition fully_faithful {C D : Category} (F : Functor C D) : Prop :=
  ∀ {x y : C}, bijective (take f : Hom C x y, F f)

theorem Yoneda_lemma {C : Category} : fully_faithful (Yoneda C) :=
  begin
    unfold [fully_faithful, bijective],
    intro x y,
    existsi take ξ : NatTrans (Yoneda C x) (Yoneda C y), ξ x 1,
    split,
    { intro f,
      unfold [Yoneda, adj, adj_hom, HomFunc, op],
      rewrite 2 Category.comp_id },
    { show ∀ ξ : NatTrans (Y_ob C x) (Y_ob C y), Y_hom C (ξ x 1) = ξ,
      from take ξ : NatTrans (Y_ob C x) (Y_ob C y),
        NatTrans.eq (take a : C,
          funext (take f: Hom C a x,
            begin
              rewrite Y_hom_ob,
              rewrite -Y_ob_hom,
              transitivity (Y_ob C y f ∘ ξ x) 1,
              { reflexivity },
              { rewrite [NatTrans.comm, ↑Type_, Y_ob_hom, Category.id_comp] }
            end)) }
  end

end category
