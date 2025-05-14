/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。参见 `LICENSE.txt` 文件。 -/

import LoVe.LoVelib


/- # LoVe 作业 1（10 分）：类型与项

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题 1（6 分）：项

我们首先声明四个新的不透明类型。 -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1（4 分）。完成以下定义，提供具有预期类型的项。

请为绑定变量使用合理的名称，例如 `a : α`、`b : β`、`c : γ`。

提示：系统化完成此操作的方法在《Hitchhiker's Guide》的 1.4 节中有描述。如其中所述，你可以在构造项时使用 `_` 作为占位符。将鼠标悬停在 `_` 上，你将看到当前的逻辑上下文。 -/

def B : (α → β) → (γ → α) → γ → β :=
  fun (f: α → β) (g: γ → α) (y: γ) ↦ f (g y)

def S : (α → β → γ) → (α → β) → α → γ :=
  fun (f: α → β → γ) (g: α → β) (a: α) ↦ f a (g a)

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  fun (f: (α → β) → γ → δ) (y: γ) (b: β) ↦ f (fun (a: α) ↦ b) y

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  fun (f: α → β) (g: α → γ) (a: α) (β: β) ↦ g a

/- 1.2（2 分）。完成以下定义。

这个看起来更难一些，但如果你遵循《Hitchhiker's Guide》中描述的方法，应该会相当直接。

注意：Peirce 的发音类似于英语单词 "purse"。 -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  fun f => f (fun g ↦ g (fun a ↦ f (fun h ↦ a)))

/- ## 问题 2（4 分）：类型推导

为你上面定义的 `B` 展示类型推导过程，使用 ASCII 或 Unicode 艺术。你可能会发现字符 `–`（用于绘制水平线）和 `⊢` 很有用。

可以自由引入缩写以避免重复大型上下文 `C`。 -/

-- 在此处写下你的解答

end LoVe
