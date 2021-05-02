import tactic

/-

Упражнения в этом файле взяты из курса Formalising Mathematics:
https://github.com/ImperialCollegeLondon/formalising-mathematics/blob/master/src/week_1/Part_D_relations.lean

Рассмотрим тип `α` и бинарные отношения над `α`: `R : α → α → Prop`.
Для бинарных отношений в Lean определены понятия рефлексивности, симметричности и транзитивности:

`reflexive R := ∀ (x : α), R x x`
`symmetric R := ∀ ⦃x y : α⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z`

Отношение `R` является отношением эквивалентности, если оно удовлетворяет всем трем определенным выше утверждениям:

`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`

В этом файле мы докажем, что существует биекция между отношениями эквивалентности на типе `α` и разбиениями элементов `α` на подмножества (чтобы не путаться, будем называть их блоками).

Определим тип разбиений элементов типа `α`. Разбиение состоит из четырех элементов:
1) `C : set (set α)` - множество блоков.
2) `Hnonempty` - доказательство того, что все блоки непусты.
3) `Hcover` - доказательство того, что любой элемент `a : α` лежит в каком-то блоке.
4) `Hdisjoint` - доказательство того, что разные блоки не пересекаются.

Ключевое слово `structure` задает тип с одним конструктором (он сгенерируется с названием `partition.mk`) и именными "полями". Если `P : partition α`, то можно писать `P.C`, `P.Hnonempty` и остальные. 
-/

@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

namespace partition

variables {α : Type} {P : partition α} {X Y : set α}

-- `X.nonempty` (или `set.nonempty X`) означает, что существует элемент, принадлежащий множеству `X`
lemma nonempty_def : X.nonempty ↔ ∃ a, a ∈ X :=
begin
  refl,
end

/-- Если `a` содержится в двух блоках `X` и `Y` -/
theorem eq_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
begin
  apply P.Hdisjoint X Y hX hY,
  use [a, haX, haY],
end

theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  have heq := eq_of_mem hX hY haX haY,
  rwa heq at hbX,
end

end partition

section equivalence_classes


variables {α : Type} (R : α → α → Prop) (hR : equivalence R)

-- Классом эквивалентности `a` назовем множество таких `b`, что `R b a`
def cl (a : α) := {b : α | R b a}

-- По определению, `b` лежит в классе эквивалентности `a`, если `R b a`
lemma mem_cl_iff {a b : α} : b ∈ cl R a ↔ R b a :=
begin
  refl
end

-- `a` принадлежит классу эквивалентности `a`
lemma mem_cl_self (hR : equivalence R) (a : α) : a ∈ cl R a :=
begin
  -- Чтобы использовать рефлексивность `R`, нужно распаковать `hR`
  -- Это можно сделать с помощью `rcases`: `rcases hR with ⟨hrefl, hsymm, htrans⟩`, или
  -- `obtain ⟨hrefl, hsymm, htrans⟩ := hR`
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  exact hrefl a,
end

-- Если `a` лежит в классе `b`, то весь класс `a` - подмножество класса `b`
lemma cl_sub_cl_of_mem_cl {a b : α} (hR : equivalence R) : a ∈ cl R b → cl R a ⊆ cl R b :=
begin
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  rintro h x Rxa,
  exact htrans Rxa h,
end

-- Напоминание: `set.subset.antisymm : X ⊆ Y → Y ⊆ X → X = Y`
lemma cl_eq_cl_of_mem_cl {a b : α} (hR : equivalence R) : a ∈ cl R b → cl R a = cl R b :=
begin
  intro h,
  apply set.subset.antisymm,
  refine cl_sub_cl_of_mem_cl R hR h,
  refine cl_sub_cl_of_mem_cl R hR _,
  exact hR.2.1 h,
end

end equivalence_classes

open partition

-- Чтобы доказать эквивалентность двух типов `X ≃ Y`, нужно построить преобразование `X → Y`, обратное преобразование `Y → X`, а также доказать, что эти два преобразования взаимнообратны

-- Далее внутри будут огромные и страшные цели, но мы их будем менять на эквивалентные с помощью тактик `change` и `show`
--   

example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
{ -- Преобразуем отношение эквивалентности `R`в разбиение:
  to_fun := λ R, {
    -- Возьмем за `C` множество классов эквивалентности всех элементов типа `α` по отношению R
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- Докажем, что такое множество блоков является разбиением. Для этого нужно доказать три свойства разбиений: `Hnonempty`, `Hcover` и `Hdisjoint`. Докажем их:
    Hnonempty := begin
      -- Любый класс эквивалентности непуст.
      cases R with R hR,
      change ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      rintro X ⟨a, rfl⟩,
      -- Крутой хак: вместо того, чтобы гипотезу вида `A = B` сохранять в переменную, можно в `rintro` и `rcases` написать `rfl` вместо названия, и (если это корректно), во всех местах `A` заменится на `B` и уйдет из контекста
      use a,
      apply mem_cl_self R hR,
    end,
    Hcover := begin
      -- Каждый элемент типа `α` содержится хотя бы в одном классе эквивалентности.
      cases R with R hR,
      change ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      intro a,
      use [cl R a],
      refine ⟨⟨a, rfl⟩, mem_cl_self R hR _⟩,
    end,
    Hdisjoint := begin
      -- Если два класса эквивалентности пересекаются, то они равны.
      cases R with R hR,
      change ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, ⟨Rac, Rbc⟩⟩,
      apply cl_eq_cl_of_mem_cl R hR,
      rcases hR with ⟨hrefl, hsymm, htrans⟩,
      refine htrans _ Rbc,
      refine hsymm Rac,
    end },
  -- Теперь построим отношение эквивалентности по разбиению
  inv_fun := λ P, 
    -- Определим бинарное отношение `R`:
    -- `R a b` если любой блок, содержащий `a`, также содержит `b`.
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- Докажем, что это отношение эквивалентности
    split,
    { -- Оно рефлексивно
      unfold reflexive, 
      rintro x A hA xA,
      exact xA,
    },
    split,
    { -- Оно симметрично
      unfold symmetric,
      rintro x y hxy X hX yX,
      obtain ⟨Y, hY, xY⟩ := P.Hcover x,
      specialize hxy Y hY xY,
      have h := eq_of_mem hX hY yX hxy,
      rwa h,
    },
    { -- Оно транзитивно
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      rintro a b c hab hbc X hX aX,
      apply hbc X hX,
      apply hab X hX,
      exact aX,
    }
  end⟩,
  -- Если начать с отношения `R` и сделать оба преобразования, снова получится `R`
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Страшная цель, но она эквивалентна следующей:
    suffices h : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
    simpa using h,
    -- ... и теперь докажем, что два отношения совпадают, тактика `ext` превратит цель в равенство для конкретных `a` и `b`
    ext a b,

    split, {
      intro h,
      specialize h a (mem_cl_self _ hR _),
      apply hR.2.1, -- симметричность
      exact h,
    }, {
      rintro hab c Rac,
      -- упростим всё до вида R _ _
      rw [cl, set.mem_set_of_eq] at *,
      -- hR.2.2 - транзитивность
      apply hR.2.2 (hR.2.1 hab) Rac,
    }
  end,
  -- Аналогично, если начать с разбиения и сделать два преобразования, получится то же разбиение
  right_inv := begin
    intro P,
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    split, {
      rintro ⟨a, ha⟩,
      obtain ⟨Y, hY, aY⟩ := P.Hcover a,
      -- Достаточно показать, что `X` это то же самое, что блок `Y`, покрывающий `a`
      suffices hXY : X = Y, {
        rwa hXY,
      },
      subst ha,
      ext t, split, {
        intro ht,
        -- Теперь, когда есть элемент типа t ∈ <страшное выражение>, его можно упростить
        -- `squeeze_simp` покажет минимальное множество использованных лемм и предложит заменить на `simp only [...]`
        -- такое применение предпочтительно, потому что в будущем множество лемм для `simp` может измениться, и старые доказательства сломаются
        -- также часто нетерминальные (те, что не закрывают цель) `simp` не слишком одобряются, поэтому предпочитают `simp only`
        squeeze_simp [cl] at ht,
        obtain ⟨Z, hZ, tZ⟩ := P.Hcover t,
        have aZ := ht Z hZ tZ,
        -- a ∈ Y ∧ a ∈ Z → Y = Z
        have hYZ := eq_of_mem hY hZ aY aZ,
        rwa hYZ,
      }, {
        simp [cl],
        rintro tY Z hZ tZ,
        refine mem_of_mem hY hZ tY tZ aY, 
      }
    }, {
      intro hX,
      obtain ⟨a, aX⟩ := P.Hnonempty X hX,
      use a,
      ext t, split, {
        simp [cl],
        rintro tX Y hY tY,
        refine mem_of_mem hX hY tX tY aX, 
      }, {
        simp [cl],
        intro h,
        obtain ⟨Y, hY, tY⟩ := P.Hcover t,
        refine mem_of_mem hY hX _ aX tY,
        -- осталось ⊢ a ∈ Y
        apply h Y hY tY,
      }
    }
  end }
