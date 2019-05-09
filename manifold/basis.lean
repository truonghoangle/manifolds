import manifold.field basis  
import linear_algebra.dual
open topological_space set vector  Euclidean


noncomputable theory
universe u

variables {α : Type }  {n : ℕ}

variable [normed_field α]

instance discrete: discrete_field α:= normed_field.to_discrete_field α


structure euclidean (α : Type*) :=
   (carrier : Type*) 
   (dim : ℕ)
  (equiv : carrier  ≃ (Π(i:fin dim),α ))

namespace euclidean
variable (E:euclidean α )

def to_vector (E:euclidean α):  E.carrier  ≃ vector α (E.dim) := equiv.trans (E.equiv) (@fun_vector α _ E.dim) 

instance : has_coe_to_sort (euclidean α)  := ⟨_, @euclidean.carrier α⟩

instance to_topological_space (E : euclidean α  ) :  topological_space E := induced (to_vector E) (by apply_instance)


def to_Top (E : euclidean α  ) : Top :=⟨E, by apply_instance⟩

instance : has_coe (euclidean α)  Top :=⟨to_Top⟩


def Euclidean_space (n : ℕ) : euclidean α  :=⟨vector α  n, n, (fun_vector n).symm ⟩

notation `α^` := Euclidean_space

instance   : add_comm_group (E:euclidean α) := equiv.add_comm_group E.equiv

instance : has_scalar α E :=  @equiv.has_scalar _ _ α E.equiv Euclidean.has_scalar
instance : mul_action α E:= equiv.mul_action E.equiv


instance :distrib_mul_action α E:=
{ distrib_mul_action. 
   smul_add  := by {repeat{intro},simp[equiv.smul_def,equiv.add_def],by library_search },
   smul_zero := by {repeat{intro},simp[equiv.smul_def,equiv.zero_def]}}



instance : semimodule α E:=
{ semimodule.
   zero_smul := by{ repeat {intro},simp[equiv.smul_def], simp[equiv.zero_def]},
   add_smul  := by {repeat {intro},simp[equiv.smul_def, equiv.add_def, semimodule.add_smul]}}

instance : module α E:={ .}
instance   : vector_space α E:={.} 

section dual

lemma equiv_vec: E ≃ₗ[α] (Π (i: fin(E.dim)), α):=
{ add:= by{simp[equiv.add_def],
 repeat {intro},
 have h:= equiv.apply_symm_apply E.equiv (E.equiv x + E.equiv y), by library_search },
  smul:= by{simp[equiv.smul_def],repeat {intro},
  have h:= equiv.apply_symm_apply E.equiv (c •(E.equiv) x), by library_search},
  .. E.equiv}


lemma dim_eq :  vector_space.dim α E = E.dim:=
by{  have h:= @dim_fun α (fin E.dim) _ _ α _ _,
  have h1:= @dim_of_field α _,
  rw[h1, mul_one,fintype.card_fin] at h,
  have H :=linear_equiv.dim_eq_lift (@equiv_vec α _ E),
  simp[h] at H, simp[H] }

lemma dim_lt: vector_space.dim α E <  cardinal.omega :=by { simp[dim_eq,cardinal.nat_lt_omega]}

lemma dual_equiv :E ≃ₗ[α] module.dual α E:=
begin
  have H:=classical.some_spec (exists_is_basis α  E) ,
  have Hy:=@is_basis.mk_eq_dim α E _ _ _ (classical.some(exists_is_basis α  E)) H,
  have H1:=@dim_lt α _ E,
  rw[Hy.symm,cardinal.lt_omega_iff_finite] at H1,
  have Hyp:= @finite.fintype _ (classical.some(exists_is_basis α  E)) H1,  
  have h:=@is_basis.to_dual_equiv α E _ _ _ (classical.some(exists_is_basis α  E)) H Hyp,
  apply h
end


def dual_equiv_std :module.dual α E ≃ₗ[α] (Π (i: fin(E.dim)), α)  :=
begin
  have h:= @dual_equiv α _ E,
  have H:= @equiv_vec α _ E,
  have hy:=@linear_equiv.trans α (module.dual α E)  E (Π (i: fin(E.dim)), α) _ _ _ _ _ _ _ h.symm H,
  apply hy
end


def dual:euclidean α  := ⟨(E →ₗ[α] α), E.dim, (@dual_equiv_std α _ E).to_equiv ⟩ 

end dual

def proj (E:euclidean α ) (i:fin (E.dim)) : E →ₗ[α] α  := (linear_map.proj i).comp ((equiv_vec E).to_linear_map) 
def std_basis (E:euclidean α) (i:fin E.dim): E := E.equiv.inv_fun (@Euclidean.std_basis α E.dim _ i) 


instance has_norm : has_norm (E:euclidean α) :=⟨λ  x,  ∥E.equiv x∥⟩

instance : has_dist (E:euclidean α )  := ⟨ λ x y, @has_dist.dist _ _ (E.equiv x) (E.equiv y)   ⟩ 

 instance metric_space  :metric_space (E:euclidean α ) :=
{ metric_space.
  dist_self:= by {intro, simp[dist], 
    have h:= (@Euclidean.normed_space α E.dim _).dist_self,
    have h1:=@h (E.equiv x),simp [dist] at h1,    apply h1  },
  dist_comm := by { simp[dist], repeat{intro},
  have h:=(@Euclidean.normed_space α E.dim _).dist_comm,
  simp [dist] at h, apply h, }, 
  dist_triangle:= by { simp[dist], repeat{intro},
  have h:=(@Euclidean.normed_space α E.dim _).dist_triangle,
  simp [dist] at h,  apply h,},
  eq_of_dist_eq_zero:= by { simp[dist], intro, intro,
  have h:=(@Euclidean.normed_space α E.dim _).eq_of_dist_eq_zero,
  simp [dist] at h,
  intro,  have heq:=@equiv.apply_eq_iff_eq _ _ E.equiv x y,  
  rwa[iff.comm] at heq,  rw [heq],   apply h,  apply a   },}


instance normed_group : normed_group (E:euclidean α) :=
{normed_group.
 dist_eq:= by {simp[norm,dist,equiv.add_def,equiv.neg_def], repeat{intro},
 have h:= (@Euclidean.normed_space α E.dim _).dist_eq, simp[norm,dist] at h, apply h,},}

instance :normed_space α (E:euclidean α):= 
{normed_space.
  norm_smul:= by {simp[norm,equiv.smul_def], repeat {intro},
  have h:= (@Euclidean.normed_space α E.dim _).norm_smul,  simp[norm,equiv.smul_def] at h,  apply h,}}

end euclidean

