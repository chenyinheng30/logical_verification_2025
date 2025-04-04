/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 家庭作业 9 (10 分 + 1 附加分): 操作语义

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1 (5 分): 算术表达式

回顾第一讲中算术表达式的类型及其求值函数： -/

#check AExp
#check eval

/- 我们引入以下缩写，表示将变量名映射到值的环境： -/

def Envir : Type :=
  String → ℤ

/- 1.1 (2 分). 完成以下算术表达式的大步语义的 Lean 定义。谓词 `BigStep` (`⟹`) 关联一个算术表达式、一个环境以及该表达式在给定环境下求值得到的值： -/

inductive BigStep : AExp × Envir → ℤ → Prop
  | num (i env) : BigStep (AExp.num i, env) i

infix:60 " ⟹ " => BigStep

/- 1.2 (1 分). 证明以下定理以验证你上面的定义。

提示：可以先证明
`(AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 2 + 2`。 -/

theorem BigStep_add_two_two (env : Envir) :
    (AExp.add (AExp.num 2) (AExp.num 2), env) ⟹ 4 :=
  sorry

/- 1.3 (2 分). 证明大步语义相对于 `eval` 函数是可靠的： -/

theorem BigStep_sound (aenv : AExp × Envir) (i : ℤ) (hstep : aenv ⟹ i) :
    eval (Prod.snd aenv) (Prod.fst aenv) = i :=
  sorry


/- ## 问题 2 (5 分 + 1 附加分): 正则表达式的语义

正则表达式是软件开发中非常流行的工具。通常，当需要分析文本输入时，会将其与正则表达式进行匹配。在这个问题中，我们定义正则表达式的语法以及正则表达式匹配字符串的含义。

我们定义 `Regex` 来表示以下文法：

    R  ::=  ∅       -- `nothing`: 不匹配任何内容
         |  ε       -- `empty`: 匹配空字符串
         |  a       -- `atom`: 匹配原子 `a`
         |  R ⬝ R    -- `concat`: 匹配两个正则表达式的连接
         |  R + R   -- `alt`: 匹配两个正则表达式中的任意一个
         |  R*      -- `star`: 匹配正则表达式的任意多次重复

注意与 WHILE 语言的粗略对应关系：

    `empty`  ~ `skip`
    `atom`   ~ 赋值
    `concat` ~ 顺序组合
    `alt`    ~ 条件语句
    `star`   ~ while 循环 -/

inductive Regex (α : Type) : Type
  | nothing : Regex α
  | empty   : Regex α
  | atom    : α → Regex α
  | concat  : Regex α → Regex α → Regex α
  | alt     : Regex α → Regex α → Regex α
  | star    : Regex α → Regex α

/- 谓词 `Matches r s` 表示正则表达式 `r` 匹配字符串 `s`（其中字符串是原子的序列）。 -/

inductive Matches {α : Type} : Regex α → List α → Prop
| empty :
  Matches Regex.empty []
| atom (a : α) :
  Matches (Regex.atom a) [a]
| concat (r₁ r₂ : Regex α) (s₁ s₂ : List α) (h₁ : Matches r₁ s₁)
    (h₂ : Matches r₂ s₂) :
  Matches (Regex.concat r₁ r₂) (s₁ ++ s₂)
| alt_left (r₁ r₂ : Regex α) (s : List α) (h : Matches r₁ s) :
  Matches (Regex.alt r₁ r₂) s
| alt_right (r₁ r₂ : Regex α) (s : List α) (h : Matches r₂ s) :
  Matches (Regex.alt r₁ r₂) s
| star_base (r : Regex α) :
  Matches (Regex.star r) []
| star_step (r : Regex α) (s s' : List α) (h₁ : Matches r s)
    (h₂ : Matches (Regex.star r) s') :
  Matches (Regex.star r) (s ++ s')

/- 引入规则对应以下情况：

* 匹配空字符串
* 匹配一个原子（例如字符）
* 匹配两个连接的正则表达式
* 匹配左侧选项
* 匹配右侧选项
* 匹配空字符串（`R*` 的基本情况）
* 匹配 `R` 后跟 `R*`（`R*` 的归纳步骤）

2.1 (1 分). 解释为什么没有 `nothing` 的规则。 -/

-- 在此输入你的答案

/- 2.2 (4 分). 证明以下反演规则。 -/

@[simp] theorem Matches_atom {α : Type} {s : List α} {a : α} :
    Matches (Regex.atom a) s ↔ s = [a] :=
  sorry

@[simp] theorem Matches_nothing {α : Type} {s : List α} :
    ¬ Matches Regex.nothing s :=
  sorry

@[simp] theorem Matches_empty {α : Type} {s : List α} :
    Matches Regex.empty s ↔ s = [] :=
  sorry

@[simp] theorem Matches_concat {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.concat r₁ r₂) s
    ↔ (∃s₁ s₂, Matches r₁ s₁ ∧ Matches r₂ s₂ ∧ s = s₁ ++ s₂) :=
  sorry

@[simp] theorem Matches_alt {α : Type} {s : List α} {r₁ r₂ : Regex α} :
    Matches (Regex.alt r₁ r₂) s ↔ (Matches r₁ s ∨ Matches r₂ s) :=
  sorry

/- 2.3 (1 附加分). 证明以下反演规则。 -/

theorem Matches_star {α : Type} {s : List α} {r : Regex α} :
    Matches (Regex.star r) s ↔
    s = []
    ∨ (∃s₁ s₂, Matches r s₁ ∧ Matches (Regex.star r) s₂ ∧ s = s₁ ++ s₂) :=
  sorry

end LoVe

