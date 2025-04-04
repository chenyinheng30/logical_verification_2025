/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 家庭作业 12（10 分 + 2 分附加分）：
# 数学的逻辑基础

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（8 分）：作为子类型的偶数

通常，表示偶自然数最方便的方法是使用更大的类型 `ℕ`，它也包含奇自然数。如果我们只想对偶数 `n` 进行量化，可以在定理陈述中添加假设 `Even n`。

另一种方法是使用子类型在类型中编码偶数性质。我们将探索这种方法。

1.1（1 分）。使用第5讲演示中引入的 `Even` 谓词，定义偶自然数的类型 `Eveℕ`。 -/

#print Even

def Eveℕ : Type :=
  sorry

/- 1.2（1 分）。证明以下关于 `Even` 谓词的定理。你将在问题1.3中需要它。

提示：定理 `add_assoc` 和 `add_comm` 可能有用。 -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  sorry

/- 1.3（2 分）。通过填充 `sorry` 占位符，定义偶数的零和加法。 -/

def Eveℕ.zero : Eveℕ :=
  sorry

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  sorry

/- 1.4（4 分）。证明偶数的加法满足交换律和结合律，并且0是其单位元。 -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m :=
  sorry

theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  sorry

theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
  sorry

theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
  sorry


/- ## 问题 2（2 分 + 2 分附加分）：希尔伯特选择

2.1（2 分附加分）。证明以下定理。

提示：

* 一个好的开始方式是对 `∃n, f n < x` 是否为真进行情况分析。

* 定理 `le_of_not_gt` 可能有用。 -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      sorry, sorry

/- 现在这个有趣的定理可以直接得出： -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 2.2（1 分）。利用你在讲座中学到的关于希尔伯特选择的知识，定义以下函数，它返回 `f` 像中最小元素的（或某个）索引。 -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  sorry

/- 2.3（1 分）。证明以下关于你定义的特征定理。 -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  sorry

end LoVe

