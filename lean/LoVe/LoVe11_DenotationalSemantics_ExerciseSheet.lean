/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe11_DenotationalSemantics_Demo


/- # LoVe 练习11：指称语义

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：单调性

1.1. 证明讲座中的以下定理。 -/

theorem Monotone_restrict {α β : Type} [PartialOrder α] (f : α → Set (β × β))
      (p : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ p) :=
  sorry

/- 1.2. 证明其相似定理。 -/

theorem Monotone_comp {α β : Type} [PartialOrder α] (f g : α → Set (β × β))
      (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry


/- ## 问题2：正则表达式

__正则表达式__（或简称__regex__）是软件开发中广泛使用的工具，用于分析文本输入。正则表达式由以下语法生成：

    R  ::=  ∅
         |  ε
         |  a
         |  R ⬝ R
         |  R + R
         |  R*

非正式地说，正则表达式的语义如下：

* `∅` 不匹配任何内容；
* `ε` 匹配空字符串；
* `a` 匹配原子 `a`；
* `R ⬝ R` 匹配两个正则表达式的连接；
* `R + R` 匹配两个正则表达式中的任意一个；
* `R*` 匹配正则表达式的任意多次重复。

注意与WHILE语言的粗略对应关系：

    `∅` ~ 发散语句（例如 `while true do skip`）
    `ε` ~ `skip`
    `a` ~ `:=`
    `⬝` ~ `;`
    `+` ~ `if then else`
    `*` ~ `while` 循环 -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- 在本练习中，我们探索正则表达式的另一种语义。即，我们可以想象原子表示二元关系，而不是字母或符号。连接对应于关系的组合，选择是并集。从数学上讲，正则表达式和二元关系都是Kleene代数的实例。

2.1. 完成以下将正则表达式转换为关系的定义。

提示：利用与WHILE语言的对应关系。 -/

def rel_of_Regex {α : Type} : Regex (Set (α × α)) → Set (α × α)
  | Regex.nothing      => ∅
  | Regex.empty        => Id
  -- 在此处补充缺失的案例

/- 2.2. 证明关于你定义的以下递归方程。 -/

theorem rel_of_Regex_Star {α : Type} (r : Regex (Set (α × α))) :
    rel_of_Regex (Regex.star r) =
    rel_of_Regex (Regex.alt (Regex.concat r (Regex.star r)) Regex.empty) :=
  sorry

end LoVe

