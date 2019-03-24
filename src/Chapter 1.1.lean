/-Partitions Part 1-/

import util

section partition_type

parameter α : Type

structure partition := 
  (box : α -> α -> Prop) 
  (is_equiv : is_equiv _ box) 
  (non_vacous : inhabited α)

def refines (pl pr : partition) := ∀ x y, pr.box x y -> pl.box x y

lemma refines_refl : ∀ p, refines p p
| p := begin simp [refines], intros, assumption end

lemma refines_trans : ∀ a b c, refines a b -> refines b c -> refines a c :=
  begin simp [refines], intros a b c ab bc x y H
              , apply (ab x y (bc x y H)) end

instance partition_preorder : preorder partition :=
{preorder 
. le := refines
, le_refl := refines_refl
, le_trans := refines_trans
}

end partition_type

section fin_partition

notation `part` n := partition (fin n)

section part_to_string_helper

parameter n : ℕ
parameter r : rel (part n)

def go : list (fin n) -> list (list (fin n))
| [] := []
| (x :: xs) :=
  match split xs with
  | (with_x, remaining) := (x :: with_x) :: go remaining
  end
def part_to_string_helper := go 

end part_to_string_helper

variable n : ℕ

def part_to_string (p : part n) : string :=
match n with
| 0 := 
| _ :=
end

end fin_partition
