import tactic

/-!

Упражнения в этом файле взяты из курса Formalising Mathematics:
https://github.com/ImperialCollegeLondon/formalising-mathematics/blob/master/src/week_1/Part_D_relations.lean

Рассмотрим тип `α` и бинарные отношения над `α`: `R : α → α → Prop`.
Для бинарных отношений в Lean определены понятия рефлексивности, симметричности и транзитивности:

`reflexive R := ∀ (x : α), R x x`
`symmetric R := ∀ ⦃x y : α⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z`

Отношение `R` является отношением эквивалентности, если оно удовлетворяет всем трем определенным выше утверждениям:

`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`

В этом файле мы построим биекцию между отношениями эквивалентности на типе `α` и разбиениями элементов `α` на подмножества (чтобы не путаться, множества в разбиении будем называть блоками).

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
  sorry,
end

theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  sorry,
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
  sorry,
end

-- Если `a` лежит в классе `b`, то весь класс `a` - подмножество класса `b`
lemma cl_sub_cl_of_mem_cl {a b : α} (hR : equivalence R) : a ∈ cl R b → cl R a ⊆ cl R b :=
begin
  sorry,
end

-- Напоминание: `set.subset.antisymm : X ⊆ Y → Y ⊆ X → X = Y`
lemma cl_eq_cl_of_mem_cl {a b : α} (hR : equivalence R) : a ∈ cl R b → cl R a = cl R b :=
begin
  sorry,
end

end equivalence_classes

open partition

-- Чтобы доказать эквивалентность двух типов `X ≃ Y`, нужно построить преобразование `X → Y`, обратное преобразование `Y → X`, а также доказать, что эти два преобразования взаимнообратны

-- Далее внутри будут огромные и страшные цели, но мы их будем менять на эквивалентные с помощью тактик `change` и `show`


example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
{ -- Преобразуем отношение эквивалентности `R` в разбиение:
  to_fun := λ R, {
    -- Возьмем за `C` множество классов эквивалентности всех элементов типа `α` по отношению R
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- Докажем, что такое множество блоков является разбиением. Для этого нужно доказать три свойства разбиений: `Hnonempty`, `Hcover` и `Hdisjoint`. Докажем их:
    Hnonempty := begin
      -- Любый класс эквивалентности непуст.
      cases R with R hR,
      change ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      sorry,
    end,
    Hcover := begin
      -- Каждый элемент типа `α` содержится хотя бы в одном классе эквивалентности.
      cases R with R hR,
      change ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      sorry,
    end,
    Hdisjoint := begin
      -- Если два класса эквивалентности пересекаются, то они равны.
      cases R with R hR,
      change ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      sorry,
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
      sorry,
    },
    split,
    { -- Оно симметрично
      unfold symmetric,
      sorry,
    },
    { -- Оно транзитивно
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      sorry,
    }
  end⟩,
  -- Если начать с отношения `R` и сделать оба преобразования, снова получится `R`
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Страшная цель, но она эквивалентна следующей:
    suffices h : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
    simpa using h,
    -- И теперь докажем, что два отношения совпадают, тактика `ext` превратит цель в ↔ для конкретных `a` и `b`
    ext a b,
    sorry,
  end,
  -- Аналогично, если начать с разбиения `P` и сделать два преобразования, получится оригинальное разбиение
  right_inv := begin
    intro P,
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    sorry,
  end }
