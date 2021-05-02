import tactic

-- Упражнения в этом файле сосредоточены на свойствах функций: инъекции, сюръекции и биекции. 
-- По большей части заимствовано из курса Formalising Mathematics:
-- https://github.com/ImperialCollegeLondon/formalising-mathematics/blob/master/src/week_1/Part_C_functions.lean
-- https://github.com/ImperialCollegeLondon/formalising-mathematics/blob/master/src/week_4/Part_A_sets.lean

open function

-- Определим namespace, чтобы не пересекаться по названиям со стандартной библиотекой
namespace itmo.lean

-- Определим типы `X, Y, Z`, функции `f : X → Y`, `g : Y → Z` и вспомогательные элементы `(x : X) (y : Y) (z : Z)` 
variables {X Y Z : Type} {f : X → Y} {g : Y → Z} (x : X) (y : Y) (z : Z)

-- Функция `f` является инъекцией, если из `f a = f b` следует, что `a = b` (то есть, для разных входов она выдает разные результаты)
lemma injective_def : injective f ↔ ∀ a b : X, f a = f b → a = b :=
begin
  -- верно по определению
  refl,
end

-- Тождественная функция id : X → X определена, как `id x = x`:
lemma id_def : id x = x :=
begin
  refl
end

/-- Тождественная функция инъективна -/
lemma injective_id : injective (id : X → X) :=
begin
  rintro a b h,
  exact h,
end

-- Композиция функций `g ∘ f` (∘ = \o или \circ) определена, как `(g ∘ f) x = g (f x)`
lemma comp_def : (g ∘ f) x = g (f x) :=
begin
  -- верно по определению
  refl,
end

/-- Композиция инъекций является инъекцией -/
lemma injective_comp (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  rintro x y h,
  apply hf,
  apply hg,
  exact h,
end

-- Функция `f : X → Y` называется сюръекцией, если для любого `y : Y` существует `x : X`, что `f x = y`
lemma surjective_def : surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  -- верно по определению
  refl
end

/-- Тождественная функция - сюръекция -/
lemma surjective_id : surjective (id : X → X) :=
begin
  intro y,
  use y,
  refl,
end

-- Композиция сюръекций является сюръекцией
lemma surjective_comp (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  intro z,
  rcases hg z with ⟨y, rfl⟩,
  rcases hf y with ⟨x, rfl⟩,
  use x,
end


-- Функция `f` называется биекцией, если она является инъекцией и сюръекцией
lemma bijective_def : bijective f ↔ injective f ∧ surjective f :=
begin
  -- верно по определению
  refl
end

-- Используйте доказанные ранее утверждения
-- Тождественная функция - биекция
lemma bijective_id : bijective (id : X → X) :=
begin
  exact ⟨injective_id, surjective_id⟩,
end

-- Композиция биекций является биекцией
lemma bijective_comp (hf : bijective f) (hg : bijective g) : bijective (g ∘ f) :=
begin
  exact ⟨injective_comp hf.1 hg.1, surjective_comp hf.2 hg.2⟩,
end


variables (S : set X) (T : set Y)

-- Образ множества `S : set X` под действием функции `f : X → Y` обозначается как `(f '' S) : set Y`
-- `y ∈ f '' S` по определению равно `∃ x : X, x ∈ S ∧ f x = y`
-- В стандартной библиотеке это называется `set.image : (X → Y) → set X → set Y` 
#check set.image
example : set.image f S = f '' S := rfl

lemma mem_image : y ∈ f '' S = ∃ x : X, x ∈ S ∧ f x = y :=
begin
  refl,
end

-- Образ тождественной функции
lemma image_id : id '' S = S :=
begin
  ext x,
  split,
  { rintro ⟨x₁, x₁S, hx₁⟩,
    rw [← hx₁, id],
    exact x₁S, },
  { intro xS,
    use x,
    rw id,
    use xS,
    -- оставшая цель закрыта с помощью `refl` после `use`
  }
end

-- `simp` справится с такой целью, потому что в стандартной библиотеке есть функция `set.image_id'`, помеченная атрибутом `@[simp]`, что включает ее в список используемых `simp` лемм 
example : id '' S = S :=  
begin
  ext, simp,
end

-- Это хорошее место, чтобы опробовать `rintro ⟨...⟩` и `refine ⟨...⟩`
-- Тактика `refine` очень похожа на `exact` и `apply`, но к тому же позволяет писать `_` в некоторых местах, генерируя цели для пропущенных аргументов
-- Например, пусть у нас есть состояние
-- x : X
-- xS : x ∈ S
-- h: (g ∘ f) x = z
-- ⊢ z ∈ g '' (f '' S)
-- После применения `refine ⟨f x, _, h⟩`, цель меняется на
-- ⊢ f x ∈ f '' S
-- Если подчеркиваний нет, и все корректно, `refine` закроет цель

lemma image_comp (S : set X) : (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z, split,
  { rintro ⟨x, xS, h⟩,
    refine ⟨f x, _, h⟩,
    refine ⟨x, xS, rfl⟩, }, 
  { rintro ⟨y, ⟨x, xS, rfl⟩, h⟩,
    refine ⟨x, xS, h⟩, }
end

-- Если `f` - инъекция, то функция `λ S, f '' S` (то есть функция, которая переводит множество `S` в `f '' S`) - тоже
-- Тактика `dsimp` (`definitional simp`) действует так же, как `simp`, но использует только равенства, верные по определению
-- С помощью `dsimp` можно упростить "очевидные" выражения, такие, как применения λ-функций:
-- `h : (λ (S : set X), f '' S) S = (λ (S : set X), f '' S) T`
-- `dsimp at h`
-- `h : f '' S = f '' T`
-- Аналогично `simp`, `dsimp only [h₁, h₂, h₃]` будет применять только леммы `h₁`, `h₂` и `h₃`, а `dsimp only at h` не будет применять дополнительных лемм (но, например, раскроет применения лямбд и подобные вещи)

-- Для себя я нашел полезным доказать лемму `image_subset_of_subset: ∀ S T, f '' S ⊆ f '' T → S ⊆ T`

lemma image_injective : injective f → injective (λ S, f '' S) :=
begin
  intro hf,
  rintro S T hST,
  simp only at hST,
  have image_subset : ∀ S T, f '' S ⊆ f '' T → S ⊆ T, {
    clear hST S T,
    rintro S T hST x xS,
    -- то же самое, что `rcases hST ⟨x, xS, rfl⟩ with  ⟨y, yT, hy⟩`
    obtain ⟨y, yT, hy⟩ := hST ⟨x, xS, rfl⟩,
    rwa (hf hy) at yT,
  },
  apply set.subset.antisymm (image_subset S T (eq.subset hST)) (image_subset T S (eq.subset hST.symm)),
end

-- Прообраз функции `f : X → Y` обозначается `f ⁻¹' : set Y → set X
-- По определению: `x ∈ f ⁻¹' T ↔ f x ∈ T`

lemma mem_preimage : x ∈ f ⁻¹' T ↔ f x ∈ T :=
begin
  refl,
end

lemma comp_preimage (T : set Z) : (g ∘ f) ⁻¹' T = f ⁻¹' (g ⁻¹' T) :=
begin
  refl,
end

lemma preimage_injective (hf : surjective f) : injective (λ T, f ⁻¹' T) :=
begin
  rintro S T hST,
  dsimp at hST,
  -- "Достаточно доказать, что ∀ {S T}, f ⁻¹' S ⊆ f ⁻¹' T → S ⊆ T"
  -- 
  suffices : ∀ {S T}, f ⁻¹' S ⊆ f ⁻¹' T → S ⊆ T, { 
    apply set.subset.antisymm (this $ eq.subset hST) (this $ eq.subset hST.symm), 
  },
  clear hST S T,
  rintro S T hST y yS, 
  obtain ⟨y₁, rfl⟩ := hf y,
  exact hST yS,  
end 

lemma image_surjective (hf : surjective f) : surjective (λ S, f '' S) :=
begin
  intro T,
  use [f ⁻¹' T],
  dsimp only,
  ext y,
  split, {
    rintro ⟨x, h, rfl⟩,
    exact h,
  }, {
    intro yt,
    obtain ⟨x, rfl⟩ := hf y,
    exact ⟨x, yt, rfl⟩,
  }
end

lemma preimage_surjective (hf : injective f) : surjective (λ S, f ⁻¹' S) :=
begin
  intro T,
  dsimp only,
  use [f '' T],
  ext x,
  split, {
    rintro ⟨x', x'T, fx'⟩,
    rwa ←(hf fx'),
  }, {
    rintro xT,
    refine ⟨x, xT, rfl⟩,
  }
end



variables (ι : Type) 

-- Образ объединения множеств `G i` под функцией `f`, равен объединению образов множеств `G i`
-- Используйте `set.mem_Union` для переписывания
lemma image_Union (G : ι → set X) :  f '' (⋃ (i : ι), G i) = ⋃ (i : ι), f '' (G i) :=
begin
  ext y,
  split, {
    dsimp only,
    rintro ⟨y, ⟨_, ⟨i, rfl⟩, yFi⟩, rfl⟩,
    rw set.mem_Union,
    refine ⟨i, y, yFi, rfl⟩,
  }, {
    rw set.mem_Union,
    rintro ⟨i, ⟨x, xFi, rfl⟩⟩,
    refine ⟨x, _, rfl⟩,
    rw set.mem_Union,
    use [i, xFi],
  }
end

-- Прообраз объединения множеств равен объединению прообразов
-- Используйте `set.mem_bUnion_iff` для переписывания
lemma preimage_bUnion (F : ι → set Y) (Z : set ι) :
  f ⁻¹' (⋃ (i ∈ Z), F i) = ⋃ (i ∈ Z), f ⁻¹' (F i) :=
begin
  ext x,
  rw [mem_preimage, set.mem_bUnion_iff, set.mem_bUnion_iff],
  refl,
end

end itmo.lean