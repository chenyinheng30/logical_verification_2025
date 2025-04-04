/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe 第11次作业（10分 + 2附加分）：指称语义

请将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

/- 以下命令为所有`Prop`启用不可计算的决策性。
参数`0`确保仅在必要时使用此功能；否则，它会使某些可计算的定义对Lean而言不可计算。
根据你如何解答问题2.2，此命令可能会对你有所帮助。 -/

attribute [instance 0] Classical.propDecidable

/- 指称语义非常适合函数式编程。在本练习中，我们将研究Lean中函数式程序的一些表示方法及其指称语义。

`Nondet`类型表示可以进行非确定性计算的函数式程序：程序可以在许多不同的计算路径/返回值之间进行选择。
完全不返回任何结果由`fail`表示，而在两个选项（由`Bool`值`true`和`false`标识）之间的非确定性选择由`choice`表示。 -/

inductive Nondet (α : Type) : Type
  | just   : α → Nondet α
  | fail   : Nondet α
  | choice : (Bool → Nondet α) → Nondet α

namespace Nondet


/- ## 问题1（5分 + 1附加分）：`Nondet`单子

`Nondet`归纳类型构成一个单子。`pure`操作符是`Nondet.just`。
`bind`定义如下： -/

def bind {α β : Type} : Nondet α → (α → Nondet β) → Nondet β
  | just a,   f => f a
  | fail,     f => fail
  | choice k, f => choice (fun b ↦ bind (k b) f)

instance : Pure Nondet :=
  { pure := just }

instance : Bind Nondet :=
  { bind := bind }

/- 1.1（5分）。证明`Nondet`的三个单子定律。

提示：

* 要展开`pure`和`>>=`的定义，调用`simp [Bind.bind, Pure.pure]`。

* 要将`f = g`简化为`∀x, f x = g x`，使用定理`funext`。 -/

theorem pure_bind {α β : Type} (a : α) (f : α → Nondet β) :
    pure a >>= f = f a :=
 sorry

theorem bind_pure {α : Type} :
    ∀na : Nondet α, na >>= pure = na :=
  sorry

theorem bind_assoc {α β γ : Type} :
    ∀(na : Nondet α) (f : α → Nondet β) (g : β → Nondet γ),
      ((na >>= f) >>= g) = (na >>= (fun a ↦ f a >>= g)) :=
  sorry

/- 函数`portmanteau`计算两个列表的混合词：`xs`和`ys`的混合词以`xs`为前缀，`ys`为后缀，并且它们有重叠部分。
我们使用`startsWith xs ys`来测试`ys`是否以`xs`为前缀。 -/

def startsWith : List ℕ → List ℕ → Bool
  | x :: xs, []      => false
  | [],      ys      => true
  | x :: xs, y :: ys => x = y && startsWith xs ys

#eval startsWith [1, 2] [1, 2, 3]
#eval startsWith [1, 2, 3] [1, 2]

def portmanteau : List ℕ → List ℕ → List (List ℕ)
| [],      ys => []
| x :: xs, ys =>
  List.map (List.cons x) (portmanteau xs ys) ++
  (if startsWith (x :: xs) ys then [ys] else [])

/- 以下是一些混合词的例子： -/

#eval portmanteau [0, 1, 2, 3] [2, 3, 4]
#eval portmanteau [0, 1] [2, 3, 4]
#eval portmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4]

/- 1.2（1附加分）。将`portmanteau`程序从`List`单子转换为`Nondet`单子。 -/

def nondetPortmanteau : List ℕ → List ℕ → Nondet (List ℕ) :=
  sorry


/- ## 问题2（5分 + 1附加分）：非确定性的指称语义

2.1（2分）。为`Nondet`给出指称语义，将其映射到所有结果的`List`中。`pure`返回一个结果，`fail`返回零个结果，`choice`组合两个选项的结果。 -/

def listSem {α : Type} : Nondet α → List α :=
  sorry

/- 检查以下行是否给出与`portmanteau`相同的输出（如果你已回答问题1.2）： -/

#reduce listSem (nondetPortmanteau [0, 1, 2, 3] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1] [2, 3, 4])
#reduce listSem (nondetPortmanteau [0, 1, 2, 1, 2] [1, 2, 1, 2, 3, 4])

/- 2.2（3分）。通常，我们并不关心所有结果，只关心第一个成功的结果。为`Nondet`给出一个语义，如果有的话，产生第一个成功的结果。你的解决方案不应使用`listSem`。 -/

noncomputable def optionSem {α : Type} : Nondet α → Option α :=
  sorry

/- 2.3（1附加分）。证明下面的定理`List_Option_compat`，展示你定义的两个语义是兼容的。

`List.head?`返回列表的头部，包装在`Option.some`中，对于空列表返回`Option.none`。它对应于我们在第5讲中称为`headOpt`的函数。 -/

theorem List_Option_compat {α : Type} :
    ∀na : Nondet α, optionSem na = List.head? (listSem na) :=
  sorry

end Nondet

end LoVe

