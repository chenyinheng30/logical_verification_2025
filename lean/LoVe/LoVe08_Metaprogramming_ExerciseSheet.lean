/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe08_Metaprogramming_Demo


/- # LoVe 练习8：元编程

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false
set_option linter.unusedTactic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 问题1：增强版`destruct_and`

回忆讲座中提到的，`destruct_and`在简单目标上会失败，例如：-/

theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
    a ∧ c :=
  sorry

/- 我们现在将通过开发一个名为`destro_and`的新策略来解决这个问题，
该策略同时应用合取式的**解构**和**引入**规则。它还会自动遍历假设而不是接受参数。
我们将分三步开发它。

1.1. 开发一个`intro_and`策略，系统地将所有形如`a ∧ b`的目标替换为两个新目标`a`和`b`，
直到所有顶层合取式都被消除。将你的策略定义为宏。 -/

#check repeat'

-- 在此处输入你的定义

theorem abcd_bd (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ d :=
  by
    intro_and
    /- 证明状态应如下：

        case left
        a b c d: Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ d -/
    repeat' sorry

theorem abcd_bacb (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by
    intro_and
    /- 证明状态应如下：

        case left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b

        case right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ a

        case right.right.left
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ c

        case right.right.right
        a b c d : Prop
        h : a ∧ (b ∧ c) ∧ d
        ⊢ b -/
    repeat' sorry

/- 1.2. 开发一个`cases_and`策略，系统地将形如`h : a ∧ b`的假设替换为两个新假设`h_left : a`和`h_right : b`，
直到所有顶层合取式都被消除。

以下是你可以遵循的伪代码：

1. 将整个`do`块包装在`withMainContext`调用中，以确保你在正确的上下文中工作。

2. 从上下文中检索假设列表。这由`getLCtx`提供。

3. 找到第一个类型（即命题）形如`_ ∧ _`的假设（=项）。要迭代，你可以使用`for … in … do`语法。要获取项的类型，可以使用`inferType`。要检查类型`ty`是否具有`_ ∧ _`的形式，可以使用`Expr.isAppOfArity ty ``And 2`（`And`前有两个反引号）。

4. 对找到的第一个假设执行案例分析。这可以通过使用`LoVelib`中提供的元程序`cases`来实现，它类似于`cases`策略但是一个元程序。要提取与假设关联的自由变量，使用`LocalDecl.fvarId`。

5. 重复（通过递归调用）。

6. 返回。

提示：在遍历局部上下文中的声明时，确保跳过任何实现细节的声明。 -/

partial def casesAnd : TacticM Unit :=
  sorry

elab "cases_and" : tactic =>
  casesAnd

theorem abcd_bd_again (a b c d : Prop) :
    a ∧ (b ∧ c) ∧ d → b ∧ d :=
  by
    intro h
    cases_and
    /- 证明状态应如下：

        case intro.intro.intro
        a b c d : Prop
        left : a
        right : d
        left_1 : b
        right_1 : c
        ⊢ b ∧ d -/
    sorry

/- 1.3. 实现一个`destro_and`策略，首先调用`cases_and`，然后调用`intro_and`，
之后尝试证明所有可以直接通过`assumption`解决的子目标。 -/

macro "destro_and" : tactic =>
  sorry

theorem abcd_bd_over_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ d :=
  by destro_and

theorem abcd_bacb_again (a b c d : Prop) (h : a ∧ (b ∧ c) ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by destro_and

theorem abd_bacb_again (a b c d : Prop) (h : a ∧ b ∧ d) :
    b ∧ (a ∧ (c ∧ b)) :=
  by
    destro_and
    /- 证明状态应大致如下：

        case intro.intro.right.right.left
        a b c d : Prop
        left : a
        left_1 : b
        right : d
        ⊢ c -/
    sorry   -- 不可证明

/- 1.4. 提供更多`destro_and`的示例，以说服自己它在更复杂的示例上也能按预期工作。 -/

-- 在此处输入你的示例


/- ## 问题2：定理查找器

我们将实现一个函数，允许我们通过出现在其陈述中的常量来查找定理。因此，给定一个常量名称列表，该函数将列出所有包含这些常量的定理。

2.1. 编写一个函数，检查一个表达式是否包含特定的常量。

提示：

* 你可以对`e`进行模式匹配并递归进行。

* `Bool`上的"非"连接词称为`not`，"或"连接词称为`||`，"与"连接词称为`&&`，相等性称为`==`。 -/

def constInExpr (name : Name) (e : Expr) : Bool :=
  sorry

/- 2.2. 编写一个函数，检查一个表达式是否包含列表中**所有**常量。

提示：你可以递归进行，或使用`List.and`和`List.map`。 -/

def constsInExpr (names : List Name) (e : Expr) : Bool :=
  sorry

/- 2.3. 开发一个策略，使用`constsInExpr`打印所有在其陈述中包含所有常量`names`的定理名称。

这段代码应与演示文件中的`proveDirect`类似。使用`ConstantInfo.type`，你可以提取与定理关联的命题。 -/

def findConsts (names : List Name) : TacticM Unit :=
  sorry

elab "find_consts" "(" names:ident+ ")" : tactic =>
  findConsts (Array.toList (Array.map getId names))

/- 测试解决方案。 -/

theorem List.a_property_of_reverse {α : Type} (xs : List α) (a : α) :
    List.concat xs a = List.reverse (a :: List.reverse xs) :=
  by
    find_consts (List.reverse)
    find_consts (List.reverse List.concat)
    sorry

end LoVe

