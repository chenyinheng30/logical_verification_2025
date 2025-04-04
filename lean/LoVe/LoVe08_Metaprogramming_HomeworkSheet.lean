/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt` 文件。 -/

import LoVe.LoVelib


/- # LoVe 家庭作业 8（10 分 + 2 附加分）：元编程

将占位符（例如 `:= sorry`）替换为你的解决方案。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 问题 1（10 分）：`safe` 策略

你将开发一个策略，该策略会穷尽地应用所有连接词和量词的安全引入和消解规则。一个规则被称为__安全的__，如果给定一个可证的目标，它总是产生可证的子目标。此外，我们要求安全规则不引入元变量（因为这些很容易被意外实例化为错误的项）。

你将分三步进行。

1.1（4 分）。开发一个 `safe_intros` 策略，该策略重复应用 `True`、`∧` 和 `↔` 的引入规则，并为 `→`/`∀` 调用 `intro _`。该策略推广了练习中的 `intro_and`。 -/

macro "safe_intros" : tactic =>
  sorry

theorem abcd (a b c d : Prop) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe_intros
    /- 证明状态应大致如下：

        case left
        a b c d : Prop
        a_1 : a
        a_2 : b
        ⊢ False

        case right.mp
        a b c d : Prop
        a_1 : a
        a_2 : c
        ⊢ d

        case right.mpr
        a b c d : Prop
        a_1 : a
        a_2 : d
        ⊢ c -/
    repeat' sorry

/- 1.2（4 分）。开发一个 `safe_cases` 策略，该策略对 `False`、`∧` (`And`) 和 `∃` (`Exists`) 进行情况分析。该策略推广了练习中的 `cases_and`。

提示：

* `Expr.isAppOfArity` 的最后一个参数是逻辑符号期望的参数数量。例如，`∧` 的参数数量是 2。

* `Bool` 上的“或”连接词称为 `||`。

提示：在遍历局部上下文中的声明时，确保跳过任何实现细节的声明。 -/

#check @False
#check @And
#check @Exists

partial def safeCases : TacticM Unit :=
  sorry

elab "safe_cases" : tactic =>
  safeCases

theorem abcdef (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    False :=
  by
    safe_cases
  /- 证明状态应大致如下：

      case intro.intro.intro
      a b c d e f : Prop
      P : ℕ → Prop
      hneg : ¬a
      hor : c ∨ d
      himp : b → e
      hiff : e ↔ f
      left : a
      w : ℕ
      h : P w
      left_1 : b
      right : c
      ⊢ False -/
    sorry

/- 1.3（2 分）。实现一个 `safe` 策略，该策略首先在所有目标上调用 `safe_intros`，然后在所有出现的子目标上调用 `safe_cases`，最后在所有出现的子子目标上尝试 `assumption`。 -/

macro "safe" : tactic =>
  sorry

theorem abcdef_abcd (a b c d e f : Prop) (P : ℕ → Prop)
      (hneg: ¬ a) (hand : a ∧ b ∧ c) (hor : c ∨ d) (himp : b → e) (hiff : e ↔ f)
      (hex : ∃x, P x) :
    a → ¬ b ∧ (c ↔ d) :=
  by
    safe
    /- 证明状态应大致如下：

        case left.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : b
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ False

        case right.mp.intro.intro.intro
        a b c d e f : Prop
        P : ℕ → Prop
        hneg : ¬a
        hor : c ∨ d
        himp : b → e
        hiff : e ↔ f
        a_1 : a
        a_2 : c
        left : a
        w : ℕ
        h : P w
        left_1 : b
        right : c
        ⊢ d -/
    repeat' sorry


/- ## 问题 2（2 附加分）：类似 `aesop` 的策略

2.1（1 附加分）。开发一个简单的类似 `aesop` 的策略。

该策略应应用所有安全的引入和消解规则。此外，它应尝试潜在不安全的规则（如 `Or.inl` 和 `False.elim`），但在某个点回溯（或并行尝试多种可能性）。迭代加深可能是一种有效的方法，或最佳优先搜索，或广度优先搜索。该策略还应尝试应用结论与目标匹配的假设，但必要时回溯。

提示：`MonadBacktrack` monad 类可能有用。

2.2（1 附加分）。在一些基准测试上测试你的策略。

你可以在我们在练习和家庭作业 3 中证明的逻辑谜题上尝试你的策略。请将这些测试包含在下面。 -/

end LoVe

