import data.finset
import data.fintype.basic
import data.set.finite
import tactic.derive_fintype


section intro

variable {α : Type*}
-- Конечность типа или множества представлена в mathlib тремя основными типами: `A : finset α`, `fintype A` и `finite A`

-- 1. finset - конструктивно конечное множество
-- `finset` = `multiset` + `nodup`
-- `multiset` = классы эквивалентности `list` по отношению "a - перестановка b"
-- Для того, чтобы применять большинство операций (добавление/объединение/...), нужен инстанс `decidable_eq α`: нужно уметь разрешимо сравнивать элементы (чтобы, например, знать `card`)

variable (A : finset α)

#check A.card
#reduce ({0,1,2,3} : finset ℕ).card
#check @finset.card_insert_of_mem


-- 2. fintype α - класс, говорящий о том, что α - конечный тип
-- fintype α = (elems [] : finset α) (complete : ∀ x : α, x ∈ elems)
-- Можно использовать @[derive fintype], для новосозданных `inductive`
-- https://github.com/leanprover-community/mathlib/pull/3772

variable [fintype α]

example : fintype bool := by show_term {apply_instance}
example : fintype (fin 10) := by show_term {apply_instance}

#check @finset.univ

@[derive fintype]
inductive test (α : Type) [fintype α] : Type
| c1 : bool → test
| c2 : (fin 2) → (fin 3) → test
| c3 : α × α → test

-- 3. finite B - доказательство конечности множества B
-- def finite (s : set α) : Prop := nonempty (fintype s)
-- `nonempty (fintype s)` - Prop-версия того, что существует элемент типа `fintype s`
-- `fintype s` - то же самое, что `fintype {x : α // x ∈ s}` или `fintype (subtype s)` - подтип `α` состоящий из пар `⟨x, h : x ∈ s⟩`
-- Удобно использовать тогда, когда в API `finset` нет того, что хочется делать с множествами, а в `set` есть

open set

variables (β : Type) (B : set β) (hB : finite B)

#check @finite.of_fintype
end intro 

-- Докажем несколько лемм про `finset`
namespace finset

variables {α : Type} {A B : finset α} [decidable_eq α]

lemma card_erase_of_mem' {x} (h : x ∈ A) : (A.erase x).card + 1 = A.card :=
begin
  rw [card_erase_of_mem h, nat.add_one, nat.succ_pred_eq_of_pos],
  refine card_pos.2 ⟨_, h⟩,
end

end finset