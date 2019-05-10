/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

-/
import         analysis.normed_space.basic
import equiv
open  set   vector  real 

local attribute [instance] classical.prop_decidable

noncomputable theory


 universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} 
variables  {n : ℕ}


variable [normed_field α]




namespace euclidean


instance  :has_scalar α (Π(i:fin n),α ) := ⟨ λ a x, (λ i, a* x i)⟩ 
lemma smul_def  (i:fin n) (a: α) (x : Π(i:fin n),α) : (a •  x) i= a * x i := rfl


instance  : mul_action α (Π(i:fin n),α ):=
{ one_smul := by {intro,  ext1, simp [smul_def]},
  mul_smul := by {repeat{intro}, ext1, simp [smul_def], apply mul_assoc },
   }

instance :distrib_mul_action α (Π(i:fin n),α ) :=
{ distrib_mul_action.
   smul_add:= by {repeat{intro},ext1, simp [smul_def], by library_search},
   smul_zero:= by {repeat{intro},ext1,simp [smul_def], by library_search},
    }


instance :semimodule α (Π(i:fin n),α ) :=
{semimodule.
 add_smul := by {repeat {intro}, ext1, simp [smul_def], by library_search},
 zero_smul:= by {repeat {intro}, ext1, simp [smul_def], by library_search}
 }


instance :module α (Π(i:fin n),α )  :={.}

instance :vector_space α (Π(i:fin n),α )  :={.}


def std_basis (i:fin n):(Π(i:fin n),α )  :=λ j, if i=j then 1 else 0

instance :normed_space α (Π(i:fin n),α ):=fintype.normed_space



end euclidean


def fun_vector (n:ℕ ):(Π(i:fin n),α )≃ vector α n :=
{ to_fun := of_fn,
  inv_fun := nth, 
  left_inv:= by {intro, ext1,apply @nth_of_fn _ n x,  },
  right_inv:= by {intro, apply @of_fn_nth n _ x }
   }



namespace pro_real

instance : add_comm_group (vector α n) := equiv.add_comm_group (fun_vector n).symm

end pro_real




