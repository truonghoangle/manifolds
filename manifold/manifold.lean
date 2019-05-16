/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

-/
import manifold.basis
open topological_space  

noncomputable theory
universes u v w

variables {α : Type} {β : Type} {γ : Type w} {n : ℕ}

variable [nondiscrete_normed_field α]

variables {E : cartesian α } 
variables {F : cartesian α } 





structure chart (X : Top) (E : cartesian α ) :=
  (iso : X ≃ₜ. E.to_Top)
  (h1 : is_open iso.to_fun.dom)
  (h2 : is_open iso.inv_fun.dom)




namespace chart
variable {X : Top}
def to_fun (c : chart X E) : X →. E := c.iso.to_fun
def inv_fun (c :chart X E) : E →. X := c.iso.inv_fun
def domain (c : chart X E) : set X := c.to_fun.dom
def codomain (c : chart X E) : set E := c.inv_fun.dom


end chart

def lift_fun (E  : cartesian α) (F  : cartesian α) (h:(E→. α) → Prop) 
 : ( E →. F )→  Prop := λ f, ∀  i: fin (F.dim),  h (pfun.lift (cartesian.proj F i).to_fun ∘. f )


def compatible_charts  {X : Top}  (h:(E→. α) → Prop) (c₁ c₂ : chart X E) : Prop :=
lift_fun E E h   (c₂.to_fun ∘. c₁.inv_fun) ∧ 
lift_fun E E h   (c₁.to_fun ∘. c₂.inv_fun)





 class manifold {α:Type} [nondiscrete_normed_field α] (E : cartesian α ) (X:Top)   :=
  (struct1 : t2_space X)
  (struct2 : second_countable_topology X)
  (charts : set (chart X E))
  (cover : ⋃₀ (chart.domain '' charts) = set.univ)



 class manifold_prop  {α:Type}  [nondiscrete_normed_field α] (E : cartesian α )  (X:Top)    extends  manifold E X      :=
  (property: (E→. α) → Prop)
  (compatible : ∀{{c₁ c₂}}, c₁  ∈  charts → c₂∈ charts   → compatible_charts property  c₁ c₂  )





