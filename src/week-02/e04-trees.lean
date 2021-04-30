import data.nat.basic
import tactic

namespace tree

-- Определим двоичное дерево, где у каждой внутренней вершины ровно два ребенка
-- Такое дерево либо состоит из одной вершины - листа, либо состоит из корня, у которого есть левое и правое поддерево
inductive Tree
| Leaf : Tree
| Branch (left : Tree) (right : Tree) : Tree

-- Аналогично можно определить без названия аргументов
inductive Tree2
| Leaf : Tree2
| Branch : Tree2 → Tree2 → Tree2

-- Откроем namespace Tree, чтобы писать Leaf и Branch вместо Tree.Leaf и Tree.Branch
open Tree

-- Для алгебраических типов данных Lean автоматически генерирует много функций и лемм (см. ниже)
#print prefix tree.Tree

/- Из них:
Инъективность конструкторов:
`Tree.Branch.inj : ∀ {l1 r1 l2 r2 : Tree}, Branch l1 r1 = Branch l2 r2 → l1 = l2 ∧ r1 = r2`

Паттерн матчинг:
Tree.cases_on : Π {C : Tree → Sort l} (n : Tree), C Leaf → (Π (left right : Tree), C (left.Branch right)) → C n
Если мы можем доказать некоторое свойство `C` для `Leaf`, а также для `Branch left right` для любых `left` и `right`, то C верно для любого дерева.
То же самое, если мы хотим определить функцию для дерева: чтобы определить функцию для дерева, нужно определить функцию на каждом из конструкторов.

Рекурсор:
Tree.rec_on : Π {C : Tree → Sort l} (n : Tree),
  C Leaf → (Π (left right : Tree), C left → C right → C (left.Branch right)) → C n
Индукция по дереву: если свойство `C` верно для Leaf и из того, что верно C left и C right, верно C (Branch left right), то C верно для любого дерева. 
Аналогично можно определить функцию для любого дерева, для `cases_on` и `rec_on` нет разницы между утверждениями про деревья и функциями от деревьев (как мы знаем, утверждения <-> типы, и доказательства <-> элементы этого типа).
-/

variables {T L R : Tree}

-- Определим функцию "количество листьев" для дерева
def leaves : Tree → ℕ
| Leaf := 1
| (Branch left right) := leaves left + leaves right

-- В примере выше важны скобки: надо явно показать, что это один аргумент типа `Tree`
-- Определите самостоятельно функцию "количество внутренних вершин" для дерева 
def internal : Tree → ℕ := sorry

-- Доказывать утверждения про деревья можно по индукции!
-- Когда цель выглядит как равенство натуральных чисел, используйте тактику `ring` или `linarith`, чтобы закрыть цель
-- Или же можете поупражняться в применении `add_assoc` и `add_comm`
lemma leaves_eq_internal_add_one : leaves T = 1 + internal T :=
begin
  induction T with L R hL hR,
  { sorry, },
  { sorry, },
end

-- Добавим также леммы для `simp`, чтобы `leaves Leaf` и `leaves (Branch l r)` автоматически редуцировалось
-- Они верны по определению, поэтому их доказательство - просто `rfl` (терм, а не тактика)
@[simp] lemma leaves_Leaf : leaves Leaf = 1 := rfl
@[simp] lemma leaves_Branch : leaves (Branch L R) = leaves L + leaves R := rfl

-- Допишите самостоятельно simp-леммы для `internal`

-- Теперь попробуйте максимально использовать simp при доказательстве
-- После включения опции строчкой ниже simp будет выводить те переписывания, что происходили
set_option trace.simplify.rewrite true

-- example : leaves T = internal T + 1 :=
-- begin
--   induction T with L R hL hR,
--   { simp, },
--   { simp [hL, hR], ring },
-- end

-- Отключим опцию, чтобы не мешалась дальше
set_option trace.simplify.rewrite false


-- Потренируйтесь перед интервью в Google и напишите функцию, разворачивающую бинарное дерево
def flip : Tree → Tree := sorry

-- И докажите, что это инволюция
lemma flip_flip : flip (flip T) = T := 
begin
  sorry,
end

-- Количество вершин в дереве не больше 2^высота - 1
-- Если вы не играли в max_minigame, то поищите в `data.nat.basic` полезные леммы про `max a b`
-- Подсказки:
-- С вычитанием ℕ работать неприятно, перейдите сначала к цели без вычитаний: для этого найдите подходящую функцию в библиотеке
-- Постарайтесь свести цель к линейному неравенству, затем вызовите `linarith`
-- Тактика `norm_num` помогает доказывать утверждения про конкретные числа, например, `1 ≤ 2`

def depth : Tree → ℕ := sorry

def size : Tree → ℕ := sorry

lemma size_le_pow2_depth_minus_one : size T ≤ 2 ^ depth T - 1 :=
begin
  sorry,
end

-- Если вы можете придумать еще что-то интересное, что можно доказать про деревья, напишите!

end tree