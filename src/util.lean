
notation `rel` a := a -> a → a

namespace list
def split 
  {α : Type} (f : α → Prop) 
  [decidable_pred f] 
  : list α -> (list α × list α)
  | [] := ([], [])
  | (x :: xs) := 
    match split xs with
      (f_true, f_false) := 
        if f x 
          then (x :: f_true, f_false) 
          else (f_true, x :: f_false)
    end

lemma sublist_well_founded : ∀ α, well_founded (@sublist α) :=
begin intros
, intr
, 
end 

end list

export list
