import tactic.ring

def rel (α : Type) : Type := α -> α -> Prop

namespace nat
lemma add_le_left_right : ∀ n m k l : nat, n ≤ m → k ≤ l → n + k ≤ m + l :=
begin intros
, transitivity (n + l)
, {apply (nat.add_le_add_left a_1)}
, {apply (nat.add_le_add_right a)}
end
end nat

namespace list

def split 
  {α : Type} (f : α → Prop) 
  [decidable_pred f] 
  : list α -> (list α × list α)
| [] := ([],[])
| (x::xs) := 
  match split xs with (f_true, f_false) := 
    if f x 
      then (x :: f_true, f_false)
      else (f_true, x :: f_false)
  end

lemma split_is_filter 
  (α : Type) (f : α -> Prop) [decidable_pred f] (l : list α) : 
  split f l = (filter f l, filter (not ∘ f) l) :=
  begin intros
  , induction l
  , { simp [split, filter] }
  , { simp [split, filter]
    , rewrite l_ih
    , tactic.unfreeze_local_instances
    , simp [decidable_pred] at _inst_1
    , simp [split._match_1]
    , have f_l_hd_dec : decidable (f l_hd)
    , {apply _inst_1}
    , by_cases (f l_hd)
    , { rewrite if_pos
      , rewrite if_pos
      , rewrite if_neg
      , apply (not_not_intro h)
      , all_goals {assumption}
      }
    , { rewrite if_neg
      , rewrite if_neg
      , rewrite if_pos
      , all_goals {exact h}
      }
    }
  end

lemma sublist_sizeof 
  : ∀ α (sub super : list α), sub <+ super -> sizeof sub ≤ sizeof super :=
have list_sizeof : ∀ α (l : list α), sizeof l = list.sizeof l 
, {simp [sizeof, has_sizeof.sizeof, list.sizeof]} 
, begin intros _ _ _ H
  , induction H
  , {reflexivity}
  , all_goals {simp [sizeof, has_sizeof.sizeof, list.sizeof]}
  , { repeat {rewrite <- list_sizeof}
    , rewrite <- (zero_add (sizeof H_l₁))
    , rewrite <- add_assoc
    , apply nat.add_le_left_right
    , apply nat.zero_le
    , exact H_ih
    }
  , { exact H_ih}
  end

end list

export list
