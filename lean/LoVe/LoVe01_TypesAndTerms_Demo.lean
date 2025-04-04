/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。详见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 前言

## 证明助手

证明助手（也称为交互式定理证明器）

* 检查并协助开发形式化证明；
* 可用于证明重大定理，而不仅限于逻辑谜题；
* 使用过程可能较为繁琐；
* 具有高度成瘾性（类似电子游戏）。

按逻辑基础分类的部分证明助手：

* 集合论：Isabelle/ZF, Metamath, Mizar；
* 简单类型论：HOL4, HOL Light, Isabelle/HOL；
* **依赖类型论**：Agda, Coq, **Lean**, Matita, PVS。


## 成功案例

数学领域：

* 四色定理（使用 Coq 证明）；
* 开普勒猜想（使用 HOL Light 和 Isabelle/HOL 证明）；
* perfectoid 空间的定义（使用 Lean 证明）。

计算机科学领域：

* 硬件验证；
* 操作系统验证；
* 编程语言理论；
* 编译器验证；
* 安全验证。


## Lean

Lean 是由 Leonardo de Moura（亚马逊云服务）自 2012 年起主导开发的证明助手。

其数学库 `mathlib` 由庞大的贡献者社区共同开发。

我们使用 Lean 4 社区版，主要依赖基础库、`mathlib4` 和 `LoVelib` 等。Lean 是一个持续发展的研究项目。

优势特性：

* 基于**归纳构造演算**依赖类型论的高度表达性逻辑系统；
* 扩展支持经典公理和商类型；
* 元编程框架；
* 现代化用户界面；
* 完善的文档体系；
* 开源项目；
* 双关语创作源泉（如 Lean Forward, Lean Together, Boolean 等）。


## 课程目标

我们希望您能：

* 掌握交互式定理证明的核心理论与技术；
* 熟悉若干应用领域；
* 培养可应用于大型项目的实践技能（作为业余爱好、硕士/博士研究或工业应用）；
* 具备迁移至其他证明助手并应用所学知识的能力；
* 达到可自主阅读学术论文的领域理解水平。

本课程既非纯粹的逻辑基础课程，也非 Lean 使用教程。Lean 是我们的工具而非终极目标。


# LoVe 演示1：类型与项

我们首先学习 Lean 的基础知识，从类型和项（表达式）开始。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Lean 概览

初步理解：

    Lean = 函数式编程 + 逻辑系统

本次课程涵盖类型与项的语法，这些内容与简单类型 λ-演算或类型化函数式编程语言（ML, OCaml, Haskell）类似。


## 类型系统

类型 `σ`, `τ`, `υ`：

* 类型变量 `α`；
* 基础类型 `T`；
* 复合类型 `T σ1 … σN`。

部分类型构造子 `T` 采用中缀表示法，例如 `→`（函数类型）。

函数箭头为右结合：
`σ₁ → σ₂ → σ₃ → τ` = `σ₁ → (σ₂ → (σ₃ → τ))`。

支持多态类型。在 Lean 中，类型变量必须使用 `∀` 绑定，例如 `∀α, α → α`。


## 项系统

项 `t`, `u`：

* 常量 `c`；
* 变量 `x`；
* 应用 `t u`；
* 匿名函数 `fun x ↦ t`（亦称 λ-表达式）。

__柯里化__：函数可以

* 完全应用（如 `f x y z` 若 `f` 最多接受3个参数）；
* 部分应用（如 `f x y`, `f x`）；
* 保持非应用状态（如 `f`）。

应用操作为左结合：`f x y z` = `((f x) y) z`。

`#check` 命令可报告参数的类型。 -/

#check ℕ
#check ℤ

#check Empty
#check Unit
#check Bool

#check ℕ → ℤ
#check ℤ → ℕ
#check Bool → ℕ → ℤ
#check (Bool → ℕ) → ℤ
#check ℕ → (Bool → ℕ) → ℤ

#check fun x : ℕ ↦ x
#check fun f : ℕ → ℕ ↦ fun g : ℕ → ℕ ↦ fun h : ℕ → ℕ ↦
  fun x : ℕ ↦ h (g (f x))
#check fun (f g h : ℕ → ℕ) (x : ℕ) ↦ h (g (f x))

/- `opaque` 定义指定类型的任意常量。 -/

opaque a : ℤ
opaque b : ℤ
opaque f : ℤ → ℤ
opaque g : ℤ → ℤ → ℤ

#check fun x : ℤ ↦ g (f (g a x)) (g x b)
#check fun x ↦ g (f (g a x)) (g x b)

#check fun x ↦ x


/- ## 类型检查与类型推断

类型检查和类型推断是可判定问题（但若加入重载或子类型等特性，该性质会迅速丧失）。

类型判断式：`C ⊢ t : σ`，表示在局部上下文 `C` 中项 `t` 具有类型 `σ`。

类型规则：

    —————————— Cst   若常量 c 全局声明为类型 σ
    C ⊢ c : σ

    —————————— Var   若 x : σ 是上下文 C 中最右侧的 x 出现
    C ⊢ x : σ

    C ⊢ t : σ → τ    C ⊢ u : σ
    ——————————————————————————— App
    C ⊢ t u : τ

    C, x : σ ⊢ t : τ
    ——————————————————————————— Fun
    C ⊢ (fun x : σ ↦ t) : σ → τ

若变量 `x` 在上下文 C 中出现多次，最右侧的声明会遮蔽之前的声明。


## 类型居住性

给定类型 `σ`，__类型居住性__问题指寻找该类型的项。该问题不可判定。

递归求解策略：

1. 若 `σ` 形如 `τ → υ`，候选居住项可以是匿名函数 `fun x ↦ _`。

2. 或者，可使用任意常量或变量 `x : τ₁ → ⋯ → τN → σ` 构造项 `x _ … _`。 -/

opaque α : Type
opaque β : Type
opaque γ : Type

def someFunOfType : (α → β → γ) → ((β → α) → β) → α → γ :=
  fun f g a ↦ f a (g (fun b ↦ a))

end LoVe
