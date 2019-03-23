/-Partitions Part 1-/

section

parameter α : Type

structure part := (box : α -> α -> Prop) (is_equiv : is_equiv _ box)

def refines (pl pr : part) := ∀ x y, pr.box x y -> pl.box x y

lemma refines_refl : ∀ p, refines p p
| p := begin simp [refines], intros, assumption end

lemma refines_trans : ∀ a b c, refines a b -> refines b c -> refines a c :=
  begin simp [refines], intros a b c ab bc x y H
              , apply (ab x y (bc x y H)) end

#print refines_trans

instance Part_preorder : preorder part :=
{preorder 
. le := refines
, le_refl := refines_refl
, le_trans :=  
}

#print  

end