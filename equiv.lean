/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

-/

import data.equiv.algebra  algebra.module data.pfun
import         analysis.normed_space.basic

universes u v w 
variables {α : Type u} {β : Type v} {γ : Type w} 
open equiv 

namespace equiv


section instances

variables (e : α ≃ β)  

protected def has_scalar [has_scalar γ β] : has_scalar γ α := ⟨λ (a:γ)  x, e.symm ( a • e x)⟩

lemma smul_def [has_scalar γ β] (a: γ) (x : α) :
  @has_scalar.smul _ _ (equiv.has_scalar e) a x = e.symm ( a • e x) := rfl

protected def mul_action [monoid γ][mul_action γ  β] : mul_action γ  α :=
{ one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_action.mul_smul],
  ..equiv.has_scalar e  }


--protected def has_dist [has_dist β]: has_dist α := 
--⟨ λ x y, @has_dist.dist _ _ (e x) (e y)   ⟩ 






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









namespace roption
noncomputable theory


variable [normed_field α]

instance : has_add (roption α) := ⟨ λ x y, ⟨x.dom ∧ y.dom, λ h, x.get (h.1)+ y.get (h.2)  ⟩  ⟩

instance   :  has_zero (roption (α ))  :=⟨some (0:α)⟩

instance   :  has_one (roption (α ))  :=⟨some (1:α)⟩

instance : has_mul (roption α) := ⟨ λ x y, ⟨x.dom ∧ y.dom, λ h, x.get (h.1) * y.get (h.2)  ⟩  ⟩

instance  : has_scalar α (roption α) := ⟨λ a f, ⟨f.dom, λ h, a* (f.get h) ⟩ ⟩


instance : has_neg (roption α) := ⟨ λ x, ⟨x.dom , λ h, -x.get h ⟩  ⟩

end roption
