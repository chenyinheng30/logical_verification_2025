/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。详见 `LICENSE.txt`。 -/

import LoVe.LoVe13_BasicMathematicalStructures_Demo


/- # LoVe 练习13：基础数学结构

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：类型类

回顾我们在第5讲中介绍的归纳类型 `Tree`： -/

#check Tree

/- 以下函数接受两棵树，并将第二棵树的副本附加到第一棵树的每个叶节点上。 -/

def Tree.graft {α : Type} : Tree α → Tree α → Tree α
  | Tree.nil,        u => u
  | Tree.node a l r, u =>
    Tree.node a (Tree.graft l u) (Tree.graft r u)

#reduce Tree.graft (Tree.node 1 Tree.nil Tree.nil)
  (Tree.node 2 Tree.nil Tree.nil)

/- 1.1. 通过对 `t` 进行结构归纳，证明以下两个定理。 -/

theorem Tree.graft_assoc {α : Type} (t u v : Tree α) :
    Tree.graft (Tree.graft t u) v = Tree.graft t (Tree.graft u v) :=
  sorry

theorem Tree.graft_nil {α : Type} (t : Tree α) :
    Tree.graft t Tree.nil = t :=
  sorry

/- 1.2. 将 `Tree` 声明为 `AddMonoid` 的实例，使用 `graft` 作为加法运算符。 -/

#print AddMonoid

instance Tree.AddMonoid {α : Type} : AddMonoid (Tree α) :=
  { add       := Tree.graft
    add_assoc :=
      sorry
    zero      := Tree.nil
    add_zero  :=
      sorry
    zero_add  :=
      sorry
    nsmul     := @nsmulRec (Tree α) (Zero.mk Tree.nil) (Add.mk Tree.graft)
  }

/- 1.3 (**选做**). 解释为什么不能将 `Tree` 与 `graft` 作为加法声明为 `AddGroup` 的实例。 -/

#print AddGroup

-- 在此输入你的解释

/- 1.4 (**选做**). 证明以下定理，说明为什么 `Tree` 与 `graft` 作为加法不构成 `AddGroup`。 -/

theorem Tree.add_left_neg_counterexample :
    ∃x : Tree ℕ, ∀y : Tree ℕ, Tree.graft y x ≠ Tree.nil :=
  sorry


/- ## 问题2：多重集与有限集

回顾讲座中的以下定义： -/

#check Finset.elems
#check List.elems

/- 2.1. 证明镜像树时节点的有限集不会改变。 -/

theorem Finset.elems_mirror (t : Tree ℕ) :
    Finset.elems (mirror t) = Finset.elems t :=
  sorry

/- 2.2. 通过提供一个树 `t` 使得 `List.elems t ≠ List.elems (mirror t)`，证明这不适用于节点的列表。

如果你定义了一个合适的反例，下面的证明将会成功。 -/

def rottenTree : Tree ℕ :=
  sorry

#eval List.elems rottenTree
#eval List.elems (mirror rottenTree)

theorem List.elems_mirror_counterexample :
    ∃t : Tree ℕ, List.elems t ≠ List.elems (mirror t) :=
  by
    apply Exists.intro rottenTree
    simp [List.elems]

end LoVe

