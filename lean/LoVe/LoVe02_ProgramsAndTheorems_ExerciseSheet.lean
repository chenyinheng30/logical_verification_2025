/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 练习2：程序与定理

将占位符（例如`:= sorry`）替换为你的解答。 -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：前驱函数

1.1. 定义类型为`ℕ → ℕ`的函数`pred`，该函数返回其参数的前驱数，若参数为0则返回0。例如：

    `pred 7 = 6`
    `pred 0 = 0` -/

def pred : ℕ → ℕ
  | Nat.zero => Nat.zero
  | Nat.succ x => x

/- 1.2. 检查你的函数是否符合预期。 -/

#eval pred 0    -- 预期: 0
#eval pred 1    -- 预期: 0
#eval pred 2    -- 预期: 1
#eval pred 3    -- 预期: 2
#eval pred 10   -- 预期: 9
#eval pred 99   -- 预期: 98


/- ## 问题2：算术表达式

考虑讲座中提到的类型`AExp`和计算表达式值的函数`eval`。你可以在文件`LoVe02_ProgramsAndTheorems_Demo.lean`中找到这些定义。快速查找的方法是：

1. 按住Control（Linux和Windows）或Command（macOS）键；
2. 将光标移动到标识符`AExp`或`eval`上；
3. 点击该标识符。 -/

#check AExp
#check eval

/- 2.1. 测试`eval`函数的行为是否符合预期。确保每个构造器至少被测试一次。你可以在测试中使用以下环境。如果除以零会发生什么？

注意`#eval`（Lean的求值命令）和`eval`（我们对`AExp`的求值函数）是无关的。 -/

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- 预期: 3
-- 在此处调用`#eval`

/- 2.2. 以下函数简化涉及加法的算术表达式。它将`0 + e`和`e + 0`简化为`e`。完善这个定义，使其也能简化涉及其他三个二元运算符的表达式。 -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  -- 在此处添加缺失的匹配模式
  -- 以下是兜底匹配模式
  | AExp.num i               => AExp.num i
  | AExp.var x               => AExp.var x
  | AExp.add e₁ e₂           => AExp.add (simplify e₁) (simplify e₂)
  | AExp.sub e₁ e₂           => AExp.sub (simplify e₁) (simplify e₂)
  | AExp.mul e₁ e₂           => AExp.mul (simplify e₁) (simplify e₂)
  | AExp.div e₁ e₂           => AExp.div (simplify e₁) (simplify e₂)

/- 2.3. `simplify`函数是否正确？实际上，如何定义它的正确性？直观上，`simplify`要正确，必须返回一个在求值时与原表达式产生相同数值的算术表达式。

给定环境`env`和表达式`e`，陈述（无需证明）简化后的`e`值与简化前的`e`值相同的性质。 -/

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  eval env (simplify e) = eval env e :=   -- 将`True`替换为你的定理陈述
  sorry   -- 保留`sorry`


/- ## 问题3（选做）：映射

3.1（选做）. 定义一个通用的`map`函数，该函数将给定函数应用于列表中的每个元素。 -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β
  | List.nil => List.nil
  | List.cons x xs => List.cons (f x) (map f xs)

#eval map (fun n ↦ n + 10) [1, 2, 3]   -- 预期: [11, 12, 13]

/- 3.2（选做）. 陈述（无需证明）`map`的函子性质作为定理。模式如下：

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

尝试为你的定理赋予有意义的名称。同时，确保尽可能通用地陈述第二个性质，适用于任意类型。 -/

-- 在此处输入你的定理陈述

theorem map_identity {α : Type} (xs: List α) :
  map (fun x ↦ x) xs = xs := sorry

theorem map_compose {α β γ: Type} (f: α → β) (g: β → γ) (xs: List α):
  map (fun x ↦ g (f x)) xs = map g (map f xs) := sorry

end LoVe
