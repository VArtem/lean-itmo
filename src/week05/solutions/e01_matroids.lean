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
lemma dep_superset {A B} : A ⊆ B → ¬m.ind A → ¬m.ind B := λ h hA hB, hA (m.ind_subset h hB)

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

@[simp] lemma base_of_univ_iff_base {A : finset α} : m.base_of univ A ↔ m.base A :=
  ⟨λ ⟨_, h_ind, h_ins⟩, ⟨h_ind, λ x hx, h_ins x (mem_univ _) hx⟩, 
   λ ⟨h_ind, h_ins⟩, ⟨subset_univ A, h_ind, λ x _ hx, h_ins x hx⟩⟩

-- Секция с доказательствами про `base_of`
section base_of

-- A независимо тогда и только тогда, когда A - база A 
lemma ind_iff_base_of_self : m.ind A ↔ m.base_of A A :=
begin
  refine ⟨λ Aind, _, base_of_ind⟩,
  refine ⟨subset.refl _, Aind, λ x hx hnx, absurd hx hnx⟩,
end

-- Все базы множества равномощны
-- Вспомните/подумайте про математическое доказательство
lemma base_of_card_eq (hA : m.base_of X A) (hB : m.base_of X B) : A.card = B.card := 
begin
  by_contradiction hne,
  wlog h : A.card < B.card := lt_or_gt_of_ne hne using [A B, B A],
  obtain ⟨w, wB, wA, winsert⟩ := m.ind_exchange _ _ (base_of_ind hA) (base_of_ind hB) h,
  refine base_of_dep_of_insert hA (base_of_subset hB wB) wA winsert,
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
    replace hAX := card_le_of_subset hAX,
    rcases ind_unbounded (X.card + 1) (by linarith) with ⟨B, -, hBX, -, Bcard⟩,
    replace hBX := card_le_of_subset hBX,
    linarith,
  },
  apply nat.le_induction, {
    use [A, subset.refl A, hAX, hA],
  }, {
    rintro n Acard ⟨B, hAB, hBX, Bind, rfl⟩,
    specialize h B hAB,
    rw base_of at h,
    push_neg at h,
    rcases h hBX Bind with ⟨w, wX, wB, w_insert⟩,
    use [insert w B],
    use [subset.trans hAB (subset_insert _ _)],
    use [insert_subset.2 ⟨wX, hBX⟩],
    use [w_insert, card_insert_of_not_mem wB],
  }
end

-- У каждого подмножества X существует база
theorem exists_base_of (m : matroid α) (X : finset α): ∃ A, m.base_of X A :=
begin
  obtain ⟨B, _, Bbase⟩ := exists_base_of_superset_of_ind (empty_subset X) m.ind_empty,
  exact ⟨B, Bbase⟩,
end

-- Мощность независимого подмножества A ⊆ X не больше мощности базы X
lemma ind_card_le_base_of_card : A ⊆ X → m.ind A → m.base_of X B → A.card ≤ B.card :=
begin
  intros hAX Aind Bbase,
  obtain ⟨T, hAT, Tbase⟩ := exists_base_of_superset_of_ind hAX Aind,
  rw base_of_card_eq Bbase Tbase,
  exact card_le_of_subset hAT,
end

end base_of

-- Теорема о базах матроида
section base

lemma base_eq_card (hA : m.base A) (hB : m.base B) : A.card = B.card := 
  by {rw [←base_of_univ_iff_base] at *, exact base_of_card_eq hA hB} 

lemma ind_subset_base : m.ind A → ∃ B, A ⊆ B ∧ m.base B := λ hA, begin
  obtain ⟨B, hAB, h_base⟩ := exists_base_of_superset_of_ind (subset_univ A) hA,
  rw base_of_univ_iff_base at h_base,
  use [B, hAB, h_base],
end

theorem exists_base : ∃ A, m.base A := 
begin
  obtain ⟨B, _, Bbase⟩ := ind_subset_base m.ind_empty,
  exact ⟨B, Bbase⟩,
end

theorem base_not_subset {A B} : m.base A → m.base B → A ⊆ B → A = B :=
begin
  rintro Abase Bbase h_subset,
  exact eq_of_subset_of_card_le h_subset (ge_of_eq $ base_eq_card Abase Bbase),
end

lemma ind_and_card_eq_card_base_iff_base {A B} (Abase : m.base A) : (m.ind B ∧ A.card = B.card) ↔ m.base B :=
begin
  split, {
    rintro ⟨Bind, Acard⟩,
    use Bind,
    intros x xB h_insert_ind,
    obtain ⟨C, Bsubset, Cbase⟩ := ind_subset_base h_insert_ind,
    replace Bsubset := card_le_of_subset Bsubset,
    rw [base_eq_card Abase Cbase] at Acard,
    rw card_insert_of_not_mem xB at Bsubset,
    linarith,
  }, {
    intro Bbase,
    exact ⟨base_ind Bbase, base_eq_card Abase Bbase⟩,
  }
end

-- Почитайте про тактику `finish`: https://leanprover-community.github.io/mathlib_docs/tactics.html#finish%20/%20clarify%20/%20safe
theorem base_exchange {A B} : m.base A → m.base B → A ≠ B → ∀ x ∈ A \ B, ∃ b ∈ (B \ A), m.base (insert b (A.erase x)) :=
begin
  intros Abase Bbase h_neq x xA,
  rcases m.ind_exchange (A.erase x) B _ Bbase.1 _ with ⟨c, cB, cA, cinsert⟩,
  {
    use c,
    rw mem_sdiff at ⊢ xA,
    use [cB],
    {
      finish,
    }, {
      apply (ind_and_card_eq_card_base_iff_base Abase).1,
      use cinsert,
      rw [card_insert_of_not_mem cA, card_erase_of_mem' xA.1],
    },
  }, { 
    exact m.ind_subset (erase_subset _ _) (base_ind Abase), 
  }, {
    rw mem_sdiff at xA,
    rw [← base_eq_card Abase Bbase, card_erase_of_mem xA.1],
    exact nat.pred_lt (card_ne_zero_of_mem xA.1),
  },
end

end base

-- Цикл матроида это минимальное по включению зависимое множество

def circuit (m : matroid α) (A : finset α) := ¬ m.ind A ∧ ∀ x ∈ A, m.ind (A.erase x)

section circuit

theorem not_circuit : ¬ m.circuit ∅ := λ ⟨empty_dep, _⟩, empty_dep m.ind_empty

lemma circuit_ssubset : m.circuit A → B ⊂ A → m.ind B :=
begin 
  rintro ⟨Anind, Aerase⟩ Bsubset,
  rw ssubset_iff at Bsubset,
  rcases Bsubset with ⟨x, xB, x_insert⟩,
  rw insert_subset at x_insert,
  cases x_insert with xA h_subset,  
  apply m.ind_subset _ (Aerase x xA),
  rw ← erase_eq_of_not_mem xB,
  exact erase_subset_erase x h_subset,
end

theorem circuit_not_subset {A B} : m.circuit A → m.circuit B → A ⊆ B → A = B :=
begin
  rintro Acirc Bcirc h_subset,
  cases @lt_or_eq_of_le _ _ A B h_subset, {
    exfalso,
    exact Acirc.1 (circuit_ssubset Bcirc h),
  }, {
    exact h,
  }
end

-- Чтобы доказать эту лемму от противного, нужно доказать утверждение вида 
-- "Если A зависимо и у него нет подмножеств-циклов, 
-- то для всех k от 0 до |A| существует зависимое множество размера k"
-- Для этого я рекомендую использовать индукцию по убыванию k
-- В mathlib это nat.decreasing_induction
lemma ind_iff_no_circuit_subset (A) : m.ind A ↔ ∀ C ⊆ A, ¬m.circuit C :=
begin
  split, {
    intros Aind C hCA Ccirc,
    refine dep_superset hCA (Ccirc.1) Aind,
  }, {
    intros h,
    by_contradiction Aind,
    suffices subsets_dep : ∀ k ≤ A.card, ∃ B ⊆ A, B.card = k ∧ ¬ m.ind B, {
      obtain ⟨B, Bsub, Bcard, Bdep⟩ := subsets_dep 0 (zero_le _),
      apply Bdep,
      convert m.ind_empty,
      rwa card_eq_zero at Bcard,
    },
    intros k k_le_card,
    refine nat.decreasing_induction _ k_le_card _, {
      rintro n ⟨B, hBA, Bcard, Bdep⟩,
      specialize h B hBA,
      rw circuit at h,
      push_neg at h,
      obtain ⟨x, xAB, h_dep_erase⟩ := h Bdep,
      refine ⟨B.erase x, subset.trans (erase_subset _ _) hBA, _, h_dep_erase⟩,
      rw ← card_erase_of_mem' xAB at Bcard,
      exact add_right_cancel Bcard,
    }, {
      use [A, subset.refl _, rfl],
    }
  }
end

lemma dep_iff_contains_circuit (A) : ¬ m.ind A ↔ ∃ C ⊆ A, m.circuit C :=
begin
  convert (not_congr $ ind_iff_no_circuit_subset A),
  simp,
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
  rw rank,
  simp only [card_empty, filter_true_of_mem, ind_empty, forall_eq, powerset_empty, sup_singleton, mem_singleton],
end

-- Если B - база A, то ранг А равен мощности B
-- Леммы про `sup` здесь полезны: `finset.sup_le` и `le_sup`
lemma rank_eq_base_of_card (Bbase : m.base_of A B) : rank m A = B.card :=
begin
  rw rank_def,
  apply nat.le_antisymm, {
    apply finset.sup_le,
    intros C hC,
    rw [mem_filter, mem_powerset] at hC,
    exact ind_card_le_base_of_card hC.1 hC.2 Bbase,
  }, {
    apply le_sup,
    rw [mem_filter, mem_powerset],
    exact ⟨base_of_subset Bbase, base_of_ind Bbase⟩,
  }
end

lemma rank_exists_base_of (m : matroid α) [decidable_pred m.ind] (A : finset α) : 
  ∃ (B : finset α), m.rank A = B.card ∧ m.base_of A B :=
begin
  obtain ⟨B, Bbase⟩ := exists_base_of m A,
  refine ⟨B, rank_eq_base_of_card Bbase, Bbase⟩,
end

theorem rank_le_card : rank m A ≤ A.card :=
begin
  obtain ⟨bA, bAcard, bAbase⟩ := rank_exists_base_of m A,
  rw bAcard,
  exact card_le_of_subset bAbase.1,
end

@[simp] lemma rank_le_of_subset (hAB : A ⊆ B) : rank m A ≤ rank m B :=
begin
  obtain ⟨bA, bAbase⟩ := exists_base_of m A,
  obtain ⟨bB, bBbase⟩ := exists_base_of m B,
  rw rank_eq_base_of_card bAbase,
  rw rank_eq_base_of_card bBbase,
  refine ind_card_le_base_of_card (subset.trans bAbase.1 hAB) bAbase.2.1 bBbase,
end

@[simp] lemma rank_ind : rank m A = A.card ↔ m.ind A :=
begin
  split, {
    intro h_card,
    obtain ⟨B, Bcard, Bbase⟩ := rank_exists_base_of m A,
    rw h_card at Bcard, 
    suffices h_eq : A = B, {
      subst h_eq,
      exact Bbase.2.1,
    },
    symmetry,
    exact eq_of_subset_of_card_le Bbase.1 (le_of_eq Bcard),
  }, {
    intro Aind,
    rw [ind_iff_base_of_self] at Aind,
    rw rank_eq_base_of_card Aind,
  }
end

lemma not_mem_sdiff_iff {x : α} {A B : finset α} : x ∉ A \ B ↔ x ∉ A ∨ x ∈ B :=
begin
  rw not_iff_comm,
  push_neg, 
  simp only [mem_sdiff, iff_self],
end

lemma card_sdiff_ℤ {A B : finset α} (hAB : A ⊆ B) : ((B \ A).card : ℤ) = (B.card : ℤ) - A.card :=  
begin
  suffices h : (B \ A).card + A.card = B.card, {
    linarith,
  },
  rw [card_sdiff hAB, nat.sub_add_cancel (card_le_of_subset hAB)],
end

-- Сложный финальный босс!
-- http://neerc.ifmo.ru/wiki/index.php?title=%D0%A0%D0%B0%D0%BD%D0%B3%D0%BE%D0%B2%D0%B0%D1%8F_%D1%84%D1%83%D0%BD%D0%BA%D1%86%D0%B8%D1%8F,_%D0%BF%D0%BE%D0%BB%D1%83%D0%BC%D0%BE%D0%B4%D1%83%D0%BB%D1%8F%D1%80%D0%BD%D0%BE%D1%81%D1%82%D1%8C

theorem rank_submodular : m.rank (A ∩ B) + m.rank (A ∪ B) ≤ m.rank A + m.rank B :=
begin
  obtain ⟨bInter, bInter_base⟩ := exists_base_of m (A ∩ B),
  have rankInter := rank_eq_base_of_card bInter_base,
  
  obtain ⟨bA, bA_sub, bA_base⟩ := exists_base_of_superset_of_ind (subset.trans bInter_base.1 (inter_subset_left _ _)) (bInter_base.2.1),
  have rankA := rank_eq_base_of_card bA_base,
  
  obtain ⟨bUnion, bUnion_sub, bUnion_base⟩ :=
    exists_base_of_superset_of_ind (subset.trans bA_base.1 (subset_union_left A B)) bA_base.2.1,
  have rankUnion := rank_eq_base_of_card bUnion_base,
  
  obtain ⟨bB, bB_base⟩ := exists_base_of m B,
  have rankB := rank_eq_base_of_card bB_base,  
  
  have indB_sub : (bUnion \ (bA \ bInter)) ⊆ B := by {
    intros x hx,
    rw [mem_sdiff, not_mem_sdiff_iff] at hx,
    rcases hx with ⟨xBunion, xA | xInter⟩, {
      have xAB := bUnion_base.1 xBunion,
      cases (mem_union.1 xAB), {
        exfalso,
        have h_insert_dep := bA_base.2.2 _ h xA,
        refine h_insert_dep (m.ind_subset _ (bUnion_base.2.1)),
        rw ← insert_eq_of_mem xBunion,
        refine insert_subset_insert x bUnion_sub,
      }, {
        exact h,
      }
    }, {
      exact mem_of_mem_inter_right (bInter_base.1 xInter),
    },
  },
  have indB_ind : m.ind (bUnion \ (bA \ bInter)) := m.ind_subset (sdiff_subset _ _) bUnion_base.2.1,
  have indB_card_le := ind_card_le_base_of_card indB_sub indB_ind bB_base,
  have indB_card : (bUnion \ (bA \ bInter)).card + bA.card = bUnion.card + bInter.card := by {
    zify,
    rw card_sdiff_ℤ (subset.trans (sdiff_subset bA bInter) bUnion_sub),        
    rw card_sdiff_ℤ bA_sub,
    ring,
  },
  rw [rankInter, rankA, rankUnion, rankB],
  linarith,
end

end rank

end matroid