import tactic

-- Если вы не работали с монадами и do-блоками раньше, почитайте туториал в интернете
-- `tactic α` - функция, работающие в контексте состояния тактики и возвращает α
-- `tactic unit` - ничего не возвращает (или же возвращает `()`)

open tactic

meta def make_nat : tactic ℕ := 
return 42

-- Как использовать результат работы других тактик внутри do-блока?
-- n ← make_nat

meta def trace_nat : tactic unit :=
do
  n ← make_nat,
  tactic.trace n

-- Как дебагать тактики?
example : false :=
begin
  trace_nat,
  sorry,
end

run_cmd trace_nat

-- Как работать с окружением в тактике?
-- Для первой цели есть функция tactic.target
#check tactic.target

meta def show_goal : tactic unit :=
do
  t ← target,
  trace t
  -- trace $ expr.to_raw_fmt t покажет полную структуру, не pretty printed

example (a b : ℤ) : a^2 + b^2 ≥ 0 :=
begin
  show_goal,
  sorry,
end

-- Для локальных гипотез: функции get_local и local_context
#check get_local
#check tactic.local_context
#check infer_type

meta def inspect_local_one (nm : name) : tactic unit :=
do
  a ← get_local nm,
  trace a,
  trace (expr.to_raw_fmt a),
  a_type ← infer_type a,
  trace a_type,
  trace (expr.to_raw_fmt a_type)

example (A : Type) (b c : A) (h : b = c) : false :=
begin
  inspect_local_one `A,
  inspect_local_one `h,
  sorry,
end

-- Для монадического программирования есть много (хоть и не так богато, как в Haskell) функций
#check list.mmap

meta def inspect_all : tactic unit :=
do
  fail "TODO"

example (A : Type) (b c : A) (h : b = c) : false :=
begin
  inspect_all,
  sorry,
end


-- Наконец, реализуем версию тактики `assumption`

meta def assump_one (e : expr) : tactic unit := sorry

meta def assump_list : list expr → tactic unit := sorry

meta def assump : tactic unit := sorry

-- Тест
example {A B C : Prop} (ha : A) (hb : B) (hc : C) : B :=
begin
  assump,
  -- sorry,
end

-- Больше упражнений: https://github.com/leanprover-community/lftcm2020/blob/master/src/exercises_sources/monday/metaprogramming.lean