/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 家庭作业6（10分）：归纳谓词

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（4分）：项的类型的类型

回忆练习5问题3中项的类型： -/

inductive Term : Type
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 1.1（2分）。定义一个归纳谓词 `IsLam`，当其参数形如 `Term.lam …` 时返回 `True`，否则返回 `False`。 -/

-- 在此处输入你的定义

/- 1.2（2分）。通过证明以下定理来验证你对问题1.1的解答： -/

theorem IsLam_lam (s : String) (t : Term) :
    IsLam (Term.lam s t) :=
  sorry

theorem not_IsLamVar (s : String) :
    ¬ IsLam (Term.var s) :=
  sorry

theorem not_IsLam_app (t u : Term) :
    ¬ IsLam (Term.app t u) :=
  sorry


/- ## 问题2（6分）：传递闭包

在数学中，二元关系 `R` 在集合 `A` 上的传递闭包 `R⁺` 可以定义为满足以下规则的最小解：

    (base) 对所有 `a, b ∈ A`，若 `a R b`，则 `a R⁺ b`；
    (step) 对所有 `a, b, c ∈ A`，若 `a R b` 且 `b R⁺ c`，则 `a R⁺ c`。

在Lean中，我们可以通过将集合 `A` 与类型 `α` 等同来定义这个概念： -/

inductive TCV1 {α : Type} (R : α → α → Prop) : α → α → Prop
  | base (a b : α)   : R a b → TCV1 R a b
  | step (a b c : α) : R a b → TCV1 R b c → TCV1 R a c

/- 2.1（2分）。规则 `(step)` 使得通过向左侧添加链接来扩展传递链变得方便。另一种定义传递闭包 `R⁺` 的方式是用以下右倾规则替换 `(step)`：

    (pets) 对所有 `a, b, c ∈ A`，若 `a R⁺ b` 且 `b R c`，则 `a R⁺ c`。

定义一个谓词 `TCV2` 来体现这种替代定义。 -/

-- 在此处输入你的定义

/- 2.2（2分）。传递闭包 `R⁺` 的另一种定义是用以下对称规则替换 `(step)` 或 `(pets)`：

    (trans) 对所有 `a, b, c ∈ A`，若 `a R⁺ b` 且 `b R⁺ c`，则 `a R⁺ c`。

定义一个谓词 `TCV3` 来体现这种替代定义。 -/

-- 在此处输入你的定义

/- 2.3（1分）。证明 `(step)` 作为关于 `TCV3` 的定理也成立。 -/

theorem TCV3_step {α : Type} (R : α → α → Prop) (a b c : α) (rab : R a b)
      (tbc : TCV3 R b c) :
    TCV3 R a c :=
  sorry

/- 2.4（1分）。通过规则归纳证明以下定理： -/

theorem TCV1_pets {α : Type} (R : α → α → Prop) (c : α) :
    ∀a b, TCV1 R a b → R b c → TCV1 R a c :=
  sorry

end LoVe

