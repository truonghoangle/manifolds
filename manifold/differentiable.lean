/-
Copyright (c) 2019 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Hoang Le Truong.

-/
import manifold.basis map
import analysis.normed_space.deriv  analysis.normed_space.bounded_linear_maps
open pfun


local attribute [instance] classical.prop_decidable


noncomputable theory
universes u v w

variables {α : Type } {β : Type v} {γ : Type w} {n : ℕ}

variable [normed_field α]



namespace diff
variables {E  : cartesian α } 
variables {F  : cartesian α   } 


def is_dif_at (f : E →. α ) (x : E) : Prop := 
∃g, @has_fderiv_at α _ _ _ _ _ (@ext_by_zero α E _ f) g x


def is_dif  (f : E →. α ) : Prop := 
(∀ x:f.dom, is_dif_at f x) ∧ (is_open f.dom)

def is_dif_map  (f : E →. F ) : Prop :=  
∀ i: fin (F.dim),  is_dif (pfun.lift (cartesian.proj F i) ∘. f )


def diff_on  (f : E →. α ) (U:set E) : Prop := ∀ x:U, is_dif_at f x 



instance : normed_space α  (E →L[α] F) := bounded_linear_map.to_normed_space


lemma exists_diff (f:E →. α ) (h:@is_dif α _ E f ) :
∀ (x:E)( H:x∈ f.dom),  ∃ g,  @has_fderiv_at α _ _ _ _ _ (ext_by_zero  f) g x :=
by {
  simp [is_dif,is_dif_at] at h,
 cases h with h h1, 
 repeat {intro},
 have h2:= @h x H,
 exact h2 
}



 
def diff (f:E →. α ) [h:@is_dif α _ E f ]: E →. cartesian.dual E:=
λ x, { dom:= x ∈ f.dom,
  get:=λ y, 
  let g:=classical.some (@exists_diff α _ E f h x y) in @is_bounded_linear_map.to_linear_map α _ E _ _ _  g (bounded_linear_map.is_bounded_linear_map g)}




def is_diff (f:E →. α ) [h:@is_dif α _ E f ]:Prop := @is_dif_map α _ E (@cartesian.dual α _ E) (@diff α _ E f h)  



structure C1_diff_map  (f : E →. F )  :=  
 (has_diff: ∀ i: fin (F.dim),  (is_dif (pfun.lift ⇑(cartesian.proj F i) ∘. f)) )
 (cont: ∀ i: fin (F.dim),   is_continuous  (@diff α _ E  (pfun.lift (cartesian.proj F i) ∘. f ) (has_diff i)))

structure C2_diff_map  (f : E →. F )  :=  
 (has_diff: ∀ i: fin (F.dim),  (is_dif (pfun.lift ⇑(cartesian.proj F i) ∘. f)) )
 (has_C1_diff: ∀ i: fin (F.dim),   @is_diff α _ E (pfun.lift (cartesian.proj F i) ∘. f ) (has_diff i)  )
 (cont: ∀ i: fin (F.dim),   is_continuous  (@diff α _ E   (pfun.lift (cartesian.proj F i) ∘. f ) (has_diff i)))




def has_diff  (f : (E →. α )) (i:fin E.dim) : roption(E →. α ) := 
{dom:= @is_dif α _ E f,
 get:=λ y, (pfun.lift (cartesian.proj (cartesian.dual E) i) ∘. (@diff  α _  E f y ))}

def C:list(fin E.dim) → (E→. α )→ Prop
| []:= λ  f, is_continuous f
| (a::l):=λ f,    C l f → ∃g , g= @has_diff  α _  E f a ∧ (∀ x,  is_continuous (g.get x))

def 𝒞_n:ℕ  → (E→. F )→ Prop :=
λ n, λ f, ∀ (l: list(fin E.dim)) (i:fin F.dim), list.length l=n →  C l (pfun.lift (cartesian.proj F i) ∘. f)



def 𝒞_infinity:  (E→. F )→ Prop :=
 λ f, ∀ n:ℕ, 𝒞_n n f






lemma const (c:α):is_dif (@const_fun α E _ c):=
by {
   rw[diff.is_dif],
   apply and.intro,
   {repeat {intro},
   rw[diff.is_dif_at,ext_const],
   have h2:= @has_fderiv_at_const α _ E _ α  _ c x,
   refine ⟨ 0 , h2 ⟩},
   { rw[pfun.dom_eq],simp[const_def],  by library_search}}


end  diff

