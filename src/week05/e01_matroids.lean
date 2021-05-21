import data.finset
import data.fintype.basic
import tactic
import week05.solutions.e00_intro

open finset

structure matroid (α : Type*) [fintype α] [decidable_eq α] :=
  (ind : set (finset α))
  (ind_empty : ind ∅)
  (ind_subset : ∀ ⦃A B⦄, A ⊆ B → ind B → ind A)
  (ind_exchange : ∀ (A B : finset α), ind A → ind B → A.card < B.card →
    (∃ (c ∈ B), (c ∉ A) ∧ ind (insert c A)))

namespace matroid

attribute [simp] matroid.ind_empty

variables {α : Type} [fintype α] [decidable_eq α] {A B X : finset α} {m : matroid α}

-- Попробуйте доказать в term mode
lemma dep_superset {A B} : A ⊆ B → ¬m.ind A → ¬m.ind B := sorry

-- Базой множества A называется независимое множество B, что B ⊆ A, и для любого x ∈ A \ B, B ∪ {x} зависимо 
-- x ∈ A \ B - неудобное определение, потому что везде придется переписывать mem_sdiff
-- Аналогично, для вставки x в B есть `insert x B`
def base_of (m : matroid α) (X A : finset α) := A ⊆ X ∧ m.ind A ∧ ∀ x ∈ X, x ∉ A → ¬m.ind (insert x A) 

lemma base_of_ind : m.base_of X A → m.ind A := λ h, h.2.1

lemma base_of_subset : m.base_of X A → A ⊆ X := λ h, h.1

lemma base_of_dep_of_insert {x} : m.base_of X A → x ∈ X → x ∉ A → ¬m.ind (insert x A) := λ h hX hA, h.2.2 x hX hA

-- База матроида - аналогично, но без ограничения на подмножество
def base (m : matroid α) (B : finset α) := m.ind B ∧ ∀ x ∉ B, ¬m.ind (insert x B)

lemma base_ind : m.base A → m.ind A := λ h, h.1

@[simp] lemma base_of_univ_iff_base {A : finset α} : m.base_of univ A ↔ m.base A := sorry

-- Секция с доказательствами про `base_of`
section base_of

-- A независимо тогда и только тогда, когда A - база A 
lemma ind_iff_base_of_self : m.ind A ↔ m.base_of A A :=
begin
  sorry,
end

-- Все базы множества равномощны
-- Вспомните/подумайте про математическое доказательство от противного
-- Тактика `wlog` поможет сократить количество случаев, когда весь контекст симметричен относительно `A и B`
lemma base_of_card_eq (hA : m.base_of X A) (hB : m.base_of X B) : A.card = B.card := 
begin
  by_contradiction hne,
  wlog h : A.card < B.card := lt_or_gt_of_ne hne using [A B, B A],
  sorry,
end

-- Любое независимое подмножество X можно достроить до базы X
-- `by_contradiction` доказывает цель от противного
-- `push_neg` проталкивает отрицания максимально внутрь утверждения или цели
-- Также может помочь `nat.le_induction`

#check @nat.le_induction

lemma exists_base_of_superset_of_ind : A ⊆ X → m.ind A → ∃ B, A ⊆ B ∧ m.base_of X B :=
begin
  intros hAX hA,
  by_contradiction,
  push_neg at h,
  suffices ind_unbounded : ∀ k ≥ A.card, ∃ B, A ⊆ B ∧ B ⊆ X ∧ m.ind B ∧ B.card = k, {
    sorry,
  },
  apply nat.le_induction, {
    sorry,
  }, {
    sorry,
  }
end

-- У каждого подмножества X существует база
theorem exists_base_of (m : matroid α) (X : finset α): ∃ A, m.base_of X A :=
begin
  sorry,
end

-- Мощность независимого подмножества A ⊆ X не больше мощности базы X
lemma ind_card_le_base_of_card : A ⊆ X → m.ind A → m.base_of X B → A.card ≤ B.card :=
begin
  sorry,
end

end base_of

-- Теорема о базах матроида
section base

lemma base_eq_card (hA : m.base A) (hB : m.base B) : A.card = B.card := sorry

lemma ind_subset_base : m.ind A → ∃ B, A ⊆ B ∧ m.base B := λ hA, begin
  sorry,
end

theorem exists_base : ∃ A, m.base A := 
begin
  sorry,
end

theorem base_not_subset {A B} : m.base A → m.base B → A ⊆ B → A = B :=
begin
  sorry,
end

lemma ind_and_card_eq_card_base_iff_base {A B} (Abase : m.base A) : (m.ind B ∧ A.card = B.card) ↔ m.base B :=
begin
  sorry,
end

-- Почитайте про тактику `finish`: https://leanprover-community.github.io/mathlib_docs/tactics.html#finish%20/%20clarify%20/%20safe
theorem base_exchange {A B} : m.base A → m.base B → A ≠ B → ∀ x ∈ A \ B, ∃ b ∈ (B \ A), m.base (insert b (A.erase x)) :=
begin
  sorry,
end

end base

-- Цикл матроида это минимальное по включению зависимое множество

def circuit (m : matroid α) (A : finset α) := ¬ m.ind A ∧ ∀ x ∈ A, m.ind (A.erase x)

section circuit

theorem not_circuit : ¬ m.circuit ∅ := λ ⟨empty_dep, _⟩, empty_dep m.ind_empty

lemma circuit_ssubset : m.circuit A → B ⊂ A → m.ind B :=
begin 
  sorry,
end

theorem circuit_not_subset {A B} : m.circuit A → m.circuit B → A ⊆ B → A = B :=
begin
  sorry,
end

-- Чтобы доказать эту лемму от противного, нужно доказать утверждение вида 
-- "Если A зависимо и у него нет подмножеств-циклов, 
-- то для всех k от 0 до |A| существует зависимое множество размера k"
-- Для этого я рекомендую использовать индукцию по убыванию k
-- В mathlib это nat.decreasing_induction
lemma ind_iff_no_circuit_subset (A) : m.ind A ↔ ∀ C ⊆ A, ¬m.circuit C :=
begin
  split, {
    sorry,
  }, {
    intros h,
    by_contradiction Aind,
    suffices subsets_dep : ∀ k ≤ A.card, ∃ B ⊆ A, B.card = k ∧ ¬ m.ind B, {
      sorry,
    },
    intros k k_le_card,
    refine nat.decreasing_induction _ k_le_card _, {
      sorry,
    }, {
      sorry,
    }
  }
end

lemma dep_iff_contains_circuit (A) : ¬ m.ind A ↔ ∃ C ⊆ A, m.circuit C :=
begin
  sorry,
end

end circuit


-- Есть несколько способов определить ранговую функцию в матроиде
-- Я выбрал следующий: возьмем все независимые подмножества A и возьмем максимальную мощность среди них
-- Для такого определения нужно, чтобы проверка на независимость в матроиде была разрешимой 

variable [decidable_pred m.ind]

def rank (m : matroid α) [decidable_pred m.ind] (A : finset α) : ℕ :=  sup (filter m.ind (powerset A)) card

section rank

@[simp] lemma rank_def : rank m A = sup (filter m.ind (powerset A)) card := rfl

@[simp] lemma rank_empty : rank m ∅ = 0 := 
begin
  sorry,
end

-- Если B - база A, то ранг А равен мощности B
-- Леммы про `sup` здесь полезны: `finset.sup_le` и `le_sup`
lemma rank_eq_base_of_card (Bbase : m.base_of A B) : rank m A = B.card :=
begin
  sorry,
end

lemma rank_exists_base_of (m : matroid α) [decidable_pred m.ind] (A : finset α) : 
  ∃ (B : finset α), m.rank A = B.card ∧ m.base_of A B :=
begin
  sorry,
end

theorem rank_le_card : rank m A ≤ A.card :=
begin
  sorry,
end

@[simp] lemma rank_le_of_subset (hAB : A ⊆ B) : rank m A ≤ rank m B :=
begin
  sorry,
end

@[simp] lemma rank_ind : rank m A = A.card ↔ m.ind A :=
begin
  sorry,
end

-- Сложный финальный босс!
-- http://neerc.ifmo.ru/wiki/index.php?title=%D0%A0%D0%B0%D0%BD%D0%B3%D0%BE%D0%B2%D0%B0%D1%8F_%D1%84%D1%83%D0%BD%D0%BA%D1%86%D0%B8%D1%8F,_%D0%BF%D0%BE%D0%BB%D1%83%D0%BC%D0%BE%D0%B4%D1%83%D0%BB%D1%8F%D1%80%D0%BD%D0%BE%D1%81%D1%82%D1%8C

theorem rank_submodular : m.rank (A ∩ B) + m.rank (A ∪ B) ≤ m.rank A + m.rank B :=
begin
  sorry,
end

end rank

end matroid