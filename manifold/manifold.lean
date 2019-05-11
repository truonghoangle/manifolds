/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

-/
import manifold.differentiable

open topological_space  

noncomputable theory
universes u v w

variables {α : Type} {β : Type} {γ : Type w} {n : ℕ}

variable [normed_field α]

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

def diff_compatible_charts {X : Top}  (c₁ c₂ : chart X E) : Prop :=
diff.is_dif_map   (c₂.to_fun ∘. c₁.inv_fun) ∧ 
diff.is_dif_map   (c₁.to_fun ∘. c₂.inv_fun)


def C_compatible_charts {X : Top} (n:ℕ) (c₁ c₂ : chart X E) : Prop :=
diff.𝒞_n n  (c₂.to_fun ∘. c₁.inv_fun) ∧ 
diff.𝒞_n n   (c₁.to_fun ∘. c₂.inv_fun)

def C_infinity_compatible_charts {X : Top}  (c₁ c₂ : chart X E) : Prop :=
diff.𝒞_infinity   (c₂.to_fun ∘. c₁.inv_fun) ∧ 
diff.𝒞_infinity    (c₁.to_fun ∘. c₂.inv_fun)


 structure manifold (E : cartesian α ) (X:Top)   :=
  (struct1 : t2_space X)
  (struct2 : second_countable_topology X)
  (charts : set (chart X E))
  (cover : ⋃₀ (chart.domain '' charts) = set.univ)


 structure diff_manifold (E : cartesian α ) (X:Top) extends manifold E X      :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → diff_compatible_charts  c₁ c₂)


 structure C_infinity_manifold (E : cartesian α) (X:Top) extends manifold E X  :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → C_infinity_compatible_charts  c₁ c₂)

 structure C_manifold (n:ℕ) (E : cartesian α ) (X:Top) extends manifold E X  :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → C_compatible_charts n c₁ c₂)



def real_manifold (E : cartesian ℝ ) := diff_manifold (E : cartesian ℝ ) 

def complex_manifold (E : cartesian ℂ ) := diff_manifold (E : cartesian ℂ )






