import standard

namespace category

structure Category :=
  (Ob : Type)
  (Hom : Ob → Ob → Type)
  (comp : Π {a b c : Ob}, Hom b c → Hom a b → Hom a c)
  (id : Π a : Ob, Hom a a)
  (comp_assoc : ∀ {a b c d : Ob} {h : Hom c d} {g : Hom b c} {f : Hom a b},
                comp (comp h g) f = comp h (comp g f))
  (comp_id : ∀ {a b : Ob} {f : Hom a b}, comp f (id a) = f)
  (id_comp : ∀ {a b : Ob} {f : Hom a b}, comp (id b) f = f)

attribute Category.Ob [coercion]
notation a `⇒` b := Category.Hom _ a b
notation g `∘` f := Category.comp _ g f
notation 1 := Category.id _ _

example (C : Category) (a b c d : C) (h : c ⇒ d) (g : b ⇒ c) (f : a ⇒ b) :
  (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
  Category.comp_assoc C

example (C : Category) (a b : C) (f : a ⇒ b) : f ∘ 1 = f := Category.comp_id C

example (C : Category) (a b : C) (f : a ⇒ b) : 1 ∘ f = f := Category.id_comp C

definition op (C : Category) : Category :=
  ⦃ Category,
    Ob := Category.Ob C,
    Hom := λ a b, Category.Hom C b a,
    comp := λ a b c g f, Category.comp C f g,
    id := Category.id C,
    comp_assoc := take a b c d h g f, eq.symm (Category.comp_assoc C),
    comp_id := take a b f, Category.id_comp C,
    id_comp := take a b f, Category.comp_id C ⦄

definition Type_as_Cat : Category :=
  ⦃ Category,
    Ob := Type,
    Hom := λ a b, a → b,
    comp := @function.comp,
    id := @id,
    comp_assoc := take a b c d h g f, rfl,
    comp_id := take a b f, rfl,
    id_comp := take a b f, rfl ⦄

structure Functor (C D : Category) :=
  (Ob : Category.Ob C → Category.Ob D)
  (Hom : Π {a b : C}, Category.Hom C a b → Category.Hom D (Ob a) (Ob b))
  (resp_comp : Π {a b c : C} {g : b ⇒ c} {f : a ⇒ b},
               Hom (g ∘ f) = Hom g ∘ Hom f)
  (resp_id : Π {a : C}, Hom (Category.id C a) = Category.id D (Ob a))

attribute Functor.Ob [coercion]
attribute Functor.Hom [coercion]

example (C D : Category) (F : Functor C D) (a b c : C) (g : b ⇒ c) (f : a ⇒ b) :
  F (g ∘ f) = F g ∘ F f :=
  Functor.resp_comp F

example (C D : Category) (F : Functor C D) (a : C) :
  F (Category.id C a) = Category.id D (F a) :=
  Functor.resp_id F

definition Functor.comp {C D E : Category} (G : Functor D E) (F : Functor C D) :
  Functor C E :=
  ⦃ Functor C E,
    Ob := take a, G (F a),
    Hom := take a b f, G (F f),
    resp_comp := take a b c g f,
      calc G (F (g ∘ f))
           = G (F g ∘ F f)     : Functor.resp_comp F ...
           = G (F g) ∘ G (F f) : Functor.resp_comp G,
    resp_id := take a,
      calc G (F 1)
           = G 1   : Functor.resp_id F ... 
           = 1     : Functor.resp_id G ⦄

definition Functor.id (C : Category) : Functor C C :=
  ⦃ Functor C C,
    Ob := id,
    Hom := λ a b, id,
    resp_comp := take a b c g f, rfl,
    resp_id := take a, rfl ⦄

definition Functor.comp_assoc {C1 C2 C3 C4 : Category}
  {F3 : Functor C3 C4} {F2 : Functor C2 C3} {F1 : Functor C1 C2} :
  Functor.comp (Functor.comp F3 F2) F1 = Functor.comp F3 (Functor.comp F2 F1) :=
  sorry

definition Functor.comp_id {C D : Category} {F : Functor C D} :
  Functor.comp F (Functor.id C) = F :=
  sorry

definition Functor.id_comp {C D : Category} {F : Functor C D} :
  Functor.comp (Functor.id D) F = F :=
  sorry

definition Cat : Category :=
  ⦃ Category,
    Ob := Category,
    Hom := Functor,
    comp := @Functor.comp,
    id := Functor.id,
    comp_assoc := @Functor.comp_assoc,
    comp_id := @Functor.comp_id,
    id_comp := @Functor.id_comp ⦄

structure NatTrans {C D : Category} (F G : Functor C D) :=
  (trans : Π a : C, F a ⇒ G a)
  (comm : ∀ {a b : C} {f : a ⇒ b}, G f ∘ trans a = trans b ∘ F f)

attribute NatTrans.trans [coercion]

example (C D : Category) (F G : Functor C D) (ξ : NatTrans F G) (a b : C) (f : a ⇒ b) :
  G f ∘ ξ a = ξ b ∘ F f :=
  NatTrans.comm ξ

definition NatTrans.comp {C D : Category} {F G H : Functor C D}
  (η : NatTrans G H) (ξ : NatTrans F G) : NatTrans F H :=
  ⦃ NatTrans F H,
    trans := λ a, η a ∘ ξ a,
    comm := take a b f,
      calc H f ∘ (η a ∘ ξ a)
           = (H f ∘ η a) ∘ ξ a : Category.comp_assoc D ...
           = (η b ∘ G f) ∘ ξ a : NatTrans.comm η ...
           = η b ∘ (G f ∘ ξ a) : Category.comp_assoc D ...
           = η b ∘ (ξ b ∘ F f) : NatTrans.comm ξ ...
           = (η b ∘ ξ b) ∘ F f : Category.comp_assoc D ⦄

definition NatTrans.id {C D : Category} (F : Functor C D) : NatTrans F F :=
  ⦃ NatTrans F F,
    trans := λ a, 1,
    comm := take a b f,
      calc F f ∘ 1
           = F f     : Category.comp_id D ...
           = 1 ∘ F f : Category.id_comp D ⦄

definition NatTrans.comp_assoc {C D : Category} {F G H K : Functor C D}
  {ζ : NatTrans H K} {η : NatTrans G H} {ξ : NatTrans F G} :
  NatTrans.comp (NatTrans.comp ζ η) ξ = NatTrans.comp ζ (NatTrans.comp η ξ) :=
  sorry

definition NatTrans.comp_id {C D : Category} {F G : Functor C D} {ξ : NatTrans F G} :
  NatTrans.comp ξ (NatTrans.id F) = ξ :=
  sorry

definition NatTrans.id_comp {C D : Category} {F G : Functor C D} {ξ : NatTrans F G} :
  NatTrans.comp (NatTrans.id G) ξ = ξ :=
  sorry

definition FuncCat (C D : Category) : Category :=
  ⦃ Category,
    Ob := Functor C D,
    Hom := NatTrans,
    comp := @NatTrans.comp C D,
    id := NatTrans.id,
    comp_assoc := @NatTrans.comp_assoc C D,
    comp_id := @NatTrans.comp_id C D,
    id_comp := @NatTrans.id_comp C D ⦄

end category
