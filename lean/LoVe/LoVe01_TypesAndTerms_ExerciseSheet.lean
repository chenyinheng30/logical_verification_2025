/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。详见 `LICENSE.txt` 文件。 -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe 练习1：类型与项

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：项

完成以下定义，将 `sorry` 标记替换为符合预期类型的项。

提示：系统性的解决方法在《Hitchhiker指南》第1.4节中有描述。如其中所述，在构造项时可以使用 `_` 作为占位符。将鼠标悬停在 `_` 上可以看到当前的逻辑上下文。 -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun a b ↦ b

/- 提供一个与 `projFst` 不同的答案。 -/

def projSnd : α → α → α :=
  fun a b ↦ a

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun f a g b ↦ g a


/- ## 问题2：类型推导

在纸上或使用ASCII/Unicode艺术展示你上面定义的 `C` 的类型推导过程。可以使用字符 `–`（绘制水平线）和 `⊢`。 -/

-- 在此处注释中或纸上写下你的解答

end LoVe
