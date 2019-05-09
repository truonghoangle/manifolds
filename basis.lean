import  topology.constructions  
import equiv
open topological_space 

noncomputable theory
universes u v 
variables {α : Type u} {β : Type v} 


structure Top :=
  (carrier : Type u)
  (struct : topological_space carrier)

namespace Top
instance : has_coe_to_sort Top := ⟨Type*, Top.carrier⟩
attribute [instance] Top.struct
def restrict (X : Top) (s : set X) : Top := ⟨subtype s, by apply_instance⟩
end Top



def is_continuous [topological_space α] [topological_space β] (f : α →. β) := continuous (f.as_subtype)

structure phomeo (X Y : Top) extends X ≃. Y :=
(continuous_to_fun  : is_continuous to_fun)
(continuous_inv_fun : is_continuous inv_fun)

infixr ` ≃ₜ. `:25 := phomeo
