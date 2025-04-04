/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe 第5次作业（10分 + 2附加分）：函数式编程

请将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（6分）：霍夫曼树

考虑以下带权二叉树的类型： -/

inductive HTree (α : Type)
  | leaf  : ℕ → α → HTree α
  | inner : ℕ → HTree α → HTree α → HTree α

/- 每个构造子对应一种节点。`HTree.leaf`节点存储一个数值权重和类型为`α`的标签，
而`HTree.inner`节点存储一个数值权重、左子树和右子树。

1.1（1分）。定义一个名为`weight`的多态Lean函数，该函数接受一个类型变量为`α`的树，
并返回树根节点的权重分量： -/

def weight {α : Type} : HTree α → ℕ :=
  sorry

/- 1.2（1分）。定义一个名为`unite`的多态Lean函数，该函数接受两棵树`l, r : HTree α`，
并返回一棵新树，满足：(1) 其左子节点为`l`；(2) 其右子节点为`r`；
(3) 其权重为`l`和`r`的权重之和。 -/

def unite {α : Type} : HTree α → HTree α → HTree α :=
  sorry

/- 1.3（2分）。考虑以下`insort`函数，该函数将一棵树`u`插入到按权重递增排序的树列表中，
并保持排序。（如果输入列表未排序，结果不一定有序。） -/

def insort {α : Type} (u : HTree α) : List (HTree α) → List (HTree α)
  | []      => [u]
  | t :: ts => if weight u ≤ weight t then u :: t :: ts else t :: insort u ts

/- 证明将树插入列表不会产生空列表： -/

theorem insort_Neq_nil {α : Type} (t : HTree α) :
    ∀ts : List (HTree α), insort t ts ≠ [] :=
  sorry

/- 1.4（2分）。再次证明上述性质，这次以"纸面"证明的形式。遵循练习中问题1.4的指南。 -/

-- 在此处输入你的纸面证明


/- ## 问题2（4分 + 2附加分）：高斯求和公式

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`： -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 2.1（2分）。证明以下由高斯在小学时发现的定理。

提示：

* `mul_add`和`add_mul`定理可能有助于乘法的推理。

* 第6讲中介绍的`linarith`策略可能有助于加法的推理。 -/

/- PAUL: 我在文件中没有看到关于`linarith`的引用。这是你在讲座中提到但未在演示文件中
         提及的内容吗？值得简要说明它是什么，或参考指南。
         实际上，我提前看了一下，第6章有相关注释。也许可以复制到这里？ -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1) :=
  sorry

/- 2.2（2分）。证明`sumUpToOfFun`的以下性质。 -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n :=
  sorry

/- 2.3（2附加分）。再次以"纸面"证明的形式证明`sumUpToOfFun_mul`。
遵循练习中问题1.4的指南。 -/

-- 在此处输入你的纸面证明

end LoVe

