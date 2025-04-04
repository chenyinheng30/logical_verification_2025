/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe 家庭作业 7（10 分 + 1 附加分）：单子

请将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（5 分）：单子的 `map` 函数

我们将为单子定义一个 `map` 函数，并从三条定律推导其所谓的函子性质。

1.1（2 分）。在 `m` 上定义 `map` 函数。注意不要与课堂演示中的 `mmap` 混淆。

提示：关键在于找到创建 `m β` 类型值的方法。遵循类型指引。列出所有可用的参数和操作（例如 `pure`、`>>=`）及其类型，看看能否像拼乐高积木一样将它们组合起来。-/

def map {m : Type → Type} [LawfulMonad m] {α β : Type} (f : α → β) (ma : m α) :
    m β := :=
  sorry

/- 1.2（1 分）。证明 `map` 的恒等律。

提示：你将需要用到 `LawfulMonad.bind_pure`。 -/

theorem map_id {m : Type → Type} [LawfulMonad m] {α : Type} (ma : m α) :
    map id ma = ma :=
  sorry

/- 1.3（2 分）。证明 `map` 的复合律。 -/

theorem map_map {m : Type → Type} [LawfulMonad m] {α β γ : Type}
      (f : α → β) (g : β → γ) (ma : m α) :
    map g (map f ma) = map (fun x ↦ g (f x)) ma :=
  sorry


/- ## 问题 2（5 分 + 1 附加分）：列表的单子结构

`List` 可以被视为一个单子，类似于 `Option` 但有多个可能的结果。它也类似于 `Set`，但结果是有序且有限的。以下代码将 `List` 设置为单子。 -/

namespace List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      f => []
  | a :: as, f => f a ++ bind as f

def pure {α : Type} (a : α) : List α :=
  [a]

/- 2.1（1 分）。证明 `bind` 在连接操作下的以下性质。 -/

theorem bind_append {α β : Type} (f : α → List β) :
    ∀as as' : List α, bind (as ++ as') f = bind as f ++ bind as' f :=
  sorry

/- 2.2（3 分）。证明 `List` 的三条定律。 -/

theorem pure_bind {α β : Type} (a : α) (f : α → List β) :
    bind (pure a) f = f a :=
  sorry

theorem bind_pure {α : Type} :
    ∀as : List α, bind as pure = as :=
  sorry

theorem bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ) :
    ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) :=
  sorry

/- 2.3（1 分）。证明以下列表特有的定律。 -/

theorem bind_pure_comp_eq_map {α β : Type} {f : α → β} :
    ∀as : List α, bind as (fun a ↦ pure (f a)) = List.map f as :=
  sorry

/- 2.4（1 附加分）。将 `List` 注册为合法的单子： -/

instance LawfulMonad : LawfulMonad List :=
  sorry

end List

end LoVe

