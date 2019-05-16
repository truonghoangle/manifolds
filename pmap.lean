import   algebra.module    data.pfun equiv


universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} 

local attribute [instance] classical.prop_decidable


namespace equiv
section instances

variables (e : α ≃ β)  

protected def has_scalar [has_scalar γ β] : has_scalar γ α := ⟨λ (a:γ)  x, e.symm ( a • e x)⟩

lemma smul_def [has_scalar γ β] (a: γ) (x : α) :
  @has_scalar.smul _ _ (equiv.has_scalar e) a x = e.symm ( a • e x) := rfl

protected def mul_action [monoid γ][mul_action γ  β] : mul_action γ  α :=
{ one_smul := by simp [smul_def, one_smul],
  mul_smul := by simp [smul_def, mul_action.mul_smul],
  ..equiv.has_scalar e  }

end instances

end equiv


def fun_one_equiv : (fin 1 → α) ≃ α :=
{ to_fun := λ x,  x 0,
  inv_fun := λ x,  (λ i:fin 1, x),
  left_inv := by {intro, simp[], ext1, apply congr_arg,
  have h:=fin.cases rfl (λ i, i.elim0),apply h},
  right_inv := by{ intro, simp[]}}




namespace pfun

protected def empty (α β : Type*) : α →. β := λx, roption.none
protected def id : α →. α := pfun.lift id
protected def comp (g : β →. γ) (f : α →. β) : α →. γ := λx, roption.bind (f x) g
infix ` ∘. `:90 := pfun.comp

def to_subtype (p : α → Prop) : α →. subtype p := λx, ⟨p x, λ h, ⟨x, h⟩⟩

def compatible (f g : α →. β) : Prop := ∀x, f x = g x

namespace compatible
  variables {f g h : α →. β}
  infix ` ~. `:50 := pfun.compatible
  protected lemma symm (h : f ~. g) : g ~. f := λx, (h x).symm
 end compatible



end pfun


structure pequiv (α : Type*) (β : Type*) :=
(to_fun    : α →. β)
(inv_fun   : β →. α)
(dom_inv_fun : ∀{{x}} (hx : x ∈ pfun.dom to_fun), to_fun.fn x hx ∈ pfun.dom inv_fun)
(dom_to_fun : ∀{{y}} (hy : y ∈ pfun.dom inv_fun), inv_fun.fn y hy ∈ pfun.dom to_fun)
(left_inv  : inv_fun ∘. to_fun ~. pfun.id)
(right_inv : to_fun ∘. inv_fun ~. pfun.id)

infixr ` ≃. `:25 := pequiv







namespace pmap

protected def has_zero [has_zero β] : has_zero (α →. β) := ⟨λ x, (0:(roption β))⟩
lemma zero_def [has_zero β] (x:α) : @has_zero.zero _ pmap.has_zero x  = (0:roption β) := rfl


protected def has_one [has_one β] : has_one (α →. β )  := ⟨λ x, (1:roption β)   ⟩
lemma one_def [has_one β] (x:α) : @has_one.one _ pmap.has_one x = (1:roption β) := rfl



protected def has_mul [has_mul β] : has_mul (α →. β ) := ⟨λ x y, λ z,  x z * y z⟩
lemma mul_def [has_mul β] (x y : α→. β) (z:α) : @has_mul.mul _ pmap.has_mul x y z=  (x z) * (y z) := rfl

protected def has_add [has_add β] : has_add(α →. β ) := ⟨λ f g, λ z,  f z + g z⟩ 
lemma add_def [has_add β] (x y : α→. β) (z:α) :  @has_add.add _ pmap.has_add x y z = x z +  y z := rfl


protected def has_inv [has_inv β] : has_inv (α →. β ) := ⟨λ x, λ y,  (x y )⁻¹⟩
lemma inv_def [has_inv β] (x : α →. β ) (y: α) : @has_inv.inv _ pmap.has_inv x y = (x y)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg (α →. β ) := ⟨λ x, λ y, -x y⟩
lemma neg_def [has_neg β] (x : α →. β ) (y:α) : @has_neg.neg _ pmap.has_neg x y = - x y := rfl


protected def has_scalar [has_scalar γ β] : has_scalar γ (α →. β ) := ⟨λ a x , λ y, a • x y⟩
lemma smul_def [has_scalar γ β] (a:γ) (x : α →. β ) (y:α) : @has_scalar.smul _ _ pmap.has_scalar a x y =  a • x y := rfl



protected def semigroup [semigroup β] : semigroup (α →. β) :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..pmap.has_mul }


protected def comm_semigroup [comm_semigroup β] : comm_semigroup (α →. β )  :=
{ mul_comm := by { repeat{intro}, ext1, simp [mul_def, mul_comm]}
  ..pmap.semigroup }


protected def monoid [monoid β] : monoid (α →. β )  :=
{ monoid.
   mul := pmap.has_mul.mul,
   mul_assoc := by simp [mul_def, mul_assoc],
   one := λ x:α, some (1:β),
  one_mul := by {intro, ext1, rw[mul_def,one_def,monoid.one_mul]},
  mul_one := by {intro, ext1, rw [mul_def, pmap.one_def,monoid.mul_one]}
  }


protected def comm_monoid [comm_monoid β] : comm_monoid (α→. β) :=
{ ..pmap.comm_semigroup,
  ..pmap.monoid  }





protected def add_semigroup [add_semigroup β] : add_semigroup (α →. β ) :=
@additive.add_semigroup _ (@pmap.semigroup _ _  multiplicative.semigroup)


protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup (α →. β ) :=
@additive.add_comm_semigroup _ (@pmap.comm_semigroup _ _  multiplicative.comm_semigroup)


protected def add_monoid [add_monoid β] : add_monoid (α →. β ) :=
@additive.add_monoid _ (@pmap.monoid _ _  multiplicative.monoid)



protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid (α →. β) :=
@additive.add_comm_monoid _ (@pmap.comm_monoid _ _ multiplicative.comm_monoid)









protected def mul_action [monoid γ][mul_action γ β] :mul_action γ (α →.β ):= 
{ one_smul := by {repeat{intro}, simp[smul_def] },
  mul_smul := by {repeat{intro},ext1, simp[smul_def,mul_smul] },
  ..pmap.has_scalar
} 

instance  add_monoid'[add_monoid β] : add_monoid (α →. β) := pmap.add_monoid

protected def distrib_mul_action [monoid γ] [add_monoid β]   [distrib_mul_action γ β] : distrib_mul_action γ (α →. β):=
{ smul_add := by {repeat{intro}, ext1,simp[smul_def,add_def,smul_add ]},
  smul_zero := by {repeat{intro}, ext1,simp only [smul_def], by library_search
 },
 ..pmap.mul_action
}


instance  add_comm_monoid'[add_comm_monoid β] : add_comm_monoid(α →. β) := pmap.add_comm_monoid








end pmap


