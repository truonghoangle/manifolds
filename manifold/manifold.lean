import manifold.differentiable

open topological_space  

noncomputable theory
universes u v w

variables {α : Type} {β : Type} {γ : Type w} {n : ℕ}

variable [normed_field α]

variables {E : euclidean α } 
variables {F : euclidean α } 





structure chart (X : Top) (E : euclidean α ) :=
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

def differentiable_compatible_charts {X : Top}  (c₁ c₂ : chart X E) : Prop :=
differentiable.is_differentiable_map   (c₂.to_fun ∘. c₁.inv_fun) ∧ 
differentiable.is_differentiable_map   (c₁.to_fun ∘. c₂.inv_fun)


def C_compatible_charts {X : Top} (n:ℕ) (c₁ c₂ : chart X E) : Prop :=
differentiable.𝒞_n n  (c₂.to_fun ∘. c₁.inv_fun) ∧ 
differentiable.𝒞_n n   (c₁.to_fun ∘. c₂.inv_fun)

def C_infinity_compatible_charts {X : Top}  (c₁ c₂ : chart X E) : Prop :=
differentiable.𝒞_infinity   (c₂.to_fun ∘. c₁.inv_fun) ∧ 
differentiable.𝒞_infinity    (c₁.to_fun ∘. c₂.inv_fun)


 structure manifold (E : euclidean α )   :=
  (carrier : Top)
  (struct2 : t2_space carrier)
  (struct3 : second_countable_topology carrier)
  (charts : set (chart carrier E))
  (cover : ⋃₀ (chart.domain '' charts) = set.univ)



 structure differentiable_manifold (E : euclidean α ) extends manifold (E)  :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → differentiable_compatible_charts  c₁ c₂)

 structure C_infinity_manifold (E : euclidean α ) extends manifold (E)  :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → C_infinity_compatible_charts  c₁ c₂)

 structure C_manifold (n:ℕ) (E : euclidean α ) extends manifold (E)  :=
  (compatible : ∀{{c₁ c₂}}, c₁ ∈ charts → c₂ ∈ charts → C_compatible_charts n c₁ c₂)



def real_manifold (E : euclidean ℝ ) := differentiable_manifold (E : euclidean ℝ )

def complex_manifold (E : euclidean ℂ ) := differentiable_manifold (E : euclidean ℂ )




namespace differentiable_manifold

def dim (M:differentiable_manifold E) :ℕ := E.dim

def curve (M:differentiable_manifold E):Prop := dim M==1

def surface (M:differentiable_manifold E):Prop := dim M==2

def threefold (M:differentiable_manifold E):Prop := dim M==3
end differentiable_manifold



