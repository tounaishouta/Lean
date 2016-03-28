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
    id := λ a, Category.id C a,
    comp_assoc := take a b c d h g f, eq.symm (Category.comp_assoc C),
    comp_id := take a b f, Category.id_comp C,
    id_comp := take a b f, Category.comp_id C ⦄

definition Type_as_Cat : Category :=
  ⦃ Category,
    Ob := Type,
    Hom := λ a b, a → b,
    comp := λ a b c g f, λ x, g (f x),
    id := λ a, λ x, x,
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
           = G (F g ∘ F f)     : Functor.resp_comp F
      ...  = G (F g) ∘ G (F f) : Functor.resp_comp G,
    resp_id := take a,
      calc G (F 1)
           = G 1   : Functor.resp_id F
      ...  = 1     : Functor.resp_id G ⦄

definition Functor.id (C : Category) : Functor C C :=
  ⦃ Functor C C,
    Ob := id,
    Hom := λ a b, id,
    resp_comp := take a b c g f, rfl,
    resp_id := take a, rfl ⦄

definition Cat : Category :=
  ⦃ Category,
    Ob := Category,
    Hom := Functor,
    comp := λ C D E, Functor.comp,
    id := λ C, Functor.id C,
    comp_assoc := sorry,
    comp_id := sorry,
    id_comp := sorry ⦄

structure NatTrans {C D : Category} (F G : Functor C D) :=
  (trans : Π a : C, F a ⇒ G a)
  (comm : ∀ {a b : C} {f : a ⇒ b}, G f ∘ trans a = trans b ∘ F f)

attribute NatTrans.trans [coercion]

example (C D : Category) (F G : Functor C D) (xi : NatTrans F G) (a b : C) (f : a ⇒ b) :
  G f ∘ xi a = xi b ∘ F f :=
  NatTrans.comm xi

definition NatTrans.comp {C D : Category} {F G H : Functor C D}
  (eta : NatTrans G H) (xi : NatTrans F G) : NatTrans F H :=
  ⦃ NatTrans F H,
    trans := λ a, eta a ∘ xi a,
    comm := take a b f,
      calc H f ∘ (eta a ∘ xi a)
           = (H f ∘ eta a) ∘ xi a : Category.comp_assoc D
      ...  = (eta b ∘ G f) ∘ xi a : NatTrans.comm eta
      ...  = eta b ∘ (G f ∘ xi a) : Category.comp_assoc D
      ...  = eta b ∘ (xi b ∘ F f) : NatTrans.comm xi
      ...  = (eta b ∘ xi b) ∘ F f : Category.comp_assoc D ⦄

definition NatTrans.id {C D : Category} (F : Functor C D) : NatTrans F F :=
  ⦃ NatTrans F F,
    trans := λ a, 1,
    comm := take a b f,
      calc F f ∘ 1
           = F f     : Category.comp_id D
      ...  = 1 ∘ F f : Category.id_comp D ⦄

definition FuncCat (C D : Category) : Category :=
  ⦃ Category,
    Ob := Functor C D,
    Hom := NatTrans,
    comp := λ F G H, NatTrans.comp,
    id := λ a, NatTrans.id a,
    comp_assoc := sorry,
    comp_id := sorry,
    id_comp := sorry ⦄

end category
