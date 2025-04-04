/- 版权声明 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。详见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示8：元编程

用户可以通过自定义策略和工具扩展Lean。这种编程方式——对证明器进行编程——被称为元编程。

Lean的元编程框架主要使用与Lean输入语言相同的概念和语法。抽象语法树（AST）会__反映__内部数据结构，例如表达式（项）。证明器的内部功能通过Lean接口暴露，我们可以用于：

* 访问当前上下文和目标；
* 统一表达式；
* 查询和修改环境；
* 设置属性。

Lean的大部分功能都是用Lean自身实现的。

应用示例：

* 证明目标转换；
* 启发式证明搜索；
* 决策过程；
* 定义生成器；
* 建议工具；
* 导出器；
* 临时自动化。

Lean元编程框架的优势：

* 用户无需学习另一种编程语言来编写元程序；可以使用与定义证明器库中普通对象相同的结构和符号。

* 库中的所有内容都可用于元编程目的。

* 元程序可以在相同的交互式环境中编写和调试，鼓励同时开发形式化库和支持自动化的风格。 -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## 策略组合子

在编写自定义策略时，我们经常需要在多个目标上重复某些操作，或在策略失败时恢复。策略组合子在此类情况下很有帮助。

`repeat'`会重复应用其参数到所有（子…子）目标，直到无法继续应用为止。 -/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/- "first"组合子 `first | ⋯ | ⋯ | ⋯`会尝试第一个参数。如果失败，则应用第二个参数。如果再次失败，则应用第三个参数。依此类推。 -/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/- `all_goals`将其参数精确地应用到每个目标一次。仅当参数在**所有**目标上都成功时才成功。 -/

/-
theorem all_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- 失败
    repeat' sorry
-/

/- `try`将其参数转换为一个永远不会失败的策略。 -/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/- `any_goals`将其参数精确地应用到每个目标一次。如果参数在**任意**目标上成功，则成功。 -/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/- `solve | ⋯ | ⋯ | ⋯`类似于`first`，但仅当其中一个参数完全证明当前目标时才成功。 -/

theorem any_goals_solve_repeat_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    repeat' sorry

/- 组合子`repeat'`容易导致无限循环： -/

/-
-- 循环
theorem repeat'_Not_example :
    ¬ Even 1 :=
  by repeat' apply Not.intro
-/


/- ## 宏 -/

/- 我们通过编写一个自定义策略作为宏来开始实际的元编程。该策略体现了我们在上面的`solve`示例中硬编码的行为： -/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

/- 让我们应用我们的自定义策略： -/

theorem intro_and_even_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/- ## 元编程单子

`MetaM`是低级的元编程单子。`TacticM`扩展了`MetaM`，增加了目标管理功能。

* `MetaM`是一个状态单子，提供对全局上下文（包括所有定义和归纳类型）、符号和属性（例如`@[simp]`定理列表）等的访问。`TacticM`额外提供对目标列表的访问。

* `MetaM`和`TacticM`的行为类似于选项单子。元程序`failure`会使单子进入错误状态。

* `MetaM`和`TacticM`支持追踪，因此我们可以使用`logInfo`显示消息。

* 与其他单子类似，`MetaM`和`TacticM`支持`for`–`in`、`continue`和`return`等命令式构造。 -/

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean版本 {Lean.versionString}"
    logInfo "所有目标："
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | []     => return
    | _ :: _ =>
      logInfo "第一个目标的目标类型："
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : α) :
    Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals
    intro_and_even


/- ## 第一个示例：假设策略

我们定义一个`hypothesis`策略，其行为与预定义的`assumption`策略基本相同。 -/

def hypothesis : TacticM Unit :=
  withMainContext
    (do
       let target ← getMainTarget
       let lctx ← getLCtx
       for ldecl in lctx do
         if ! LocalDecl.isImplementationDetail ldecl then
           let eq ← isDefEq (LocalDecl.type ldecl) target
           if eq then
             let goal ← getMainGoal
             MVarId.assign goal (LocalDecl.toExpr ldecl)
             return
       failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
      (hpa : p a) :
    p a :=
  by hypothesis


/- ## 表达式

元编程框架围绕表达式或项的`Expr`类型展开。 -/

#print Expr


/- ### 名称

我们可以使用反引号创建字面名称：

* 单个反引号的名称`n不会被检查是否存在。

* 双反引号的名称``n会被解析和检查。 -/

#check `x
#eval `x
#eval `Even          -- 错误
#eval `LoVe.Even     -- 次优
#eval ``Even
/-
#eval ``EvenThough   -- 失败
-/


/- ### 常量 -/

#check Expr.const

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/- ### 排序（第12讲） -/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))


/- ### 自由变量 -/

#check Expr.fvar

#check FVarId.mk `n
#eval ppExpr (Expr.fvar (FVarId.mk `n))


/- ### 元变量 -/

#check Expr.mvar


/- ### 应用 -/

#check Expr.app

#eval ppExpr (Expr.app (Expr.const ``Nat.succ [])
  (Expr.const ``Nat.zero []))


/- ### 匿名函数和绑定变量 -/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0)
  BinderInfo.default)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat [])
  (Expr.lam `y (Expr.const ``Nat []) (Expr.bvar 1)
     BinderInfo.default)
  BinderInfo.default)


/- ### 依赖函数类型 -/

#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat [])
  (Expr.app (Expr.const ``Even []) (Expr.bvar 0))
  BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat [])
  (Expr.const `Bool []) BinderInfo.default)


/- ### 其他构造器 -/

#check Expr.letE
#check Expr.lit
#check Expr.mdata
#check Expr.proj


/- ## 第二个示例：合取析构策略

我们定义一个`destruct_and`策略，用于自动化析构前提中的`∧`，自动化如下证明： -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  And.right (And.right h)

/- 我们的策略依赖于一个辅助函数，该函数以假设`h`作为表达式参数： -/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
       let target ← getMainTarget
       let P ← inferType hP
       let eq ← isDefEq P target
       if eq then
         let goal ← getMainGoal
         MVarId.assign goal hP
         return true
       else
         match Expr.and? P with
         | Option.none        => return false
         | Option.some (Q, R) =>
           let hQ ← mkAppM ``And.left #[hP]
           let success ← destructAndExpr hQ
           if success then
             return true
           else
             let hR ← mkAppM ``And.right #[hP]
             destructAndExpr hR)

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
    (do
       let h ← getFVarFromUserName name
       let success ← destructAndExpr h
       if ! success then
         failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (getId h)

/- 让我们验证我们的策略是否有效： -/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  by destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  by destruct_and h

/-
theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
    a ∧ c :=
  by destruct_and h   -- 失败
-/


/- ## 第三个示例：直接证明查找器

最后，我们实现一个`prove_direct`工具，遍历数据库中的所有定理，检查是否可以使用其中之一证明当前目标。 -/

def isTheorem : ConstantInfo → Bool
  | ConstantInfo.axiomInfo _ => true
  | ConstantInfo.thmInfo _   => true
  | _                        => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) :
  TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac₁
    let subgoals₁ ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals₁ do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned then
        setGoals [subgoal]
        tac₂
        let subgoals₂ ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals₂
    setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info)
        in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"由 {name} 直接证明"
          setGoals (List.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect

/- 让我们验证我们的策略是否有效： -/

theorem Nat.symm (x y : ℕ) (h : x = y) :
    y = x :=
  by prove_direct

theorem Nat.symm_manual (x y : ℕ) (h : x = y) :
    y = x :=
  by
    apply symm
    hypothesis

theorem Nat.trans (x y z : ℕ) (hxy : x = y) (hyz : y = z) :
    x = z :=
  by prove_direct

theorem List.reverse_twice (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by prove_direct

/- Lean有`apply?`： -/

theorem List.reverse_twice_apply? (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by apply?

end LoVe

