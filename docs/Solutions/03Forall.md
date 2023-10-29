```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Instances.Real

open Function

namespace Forall
```

# 全称量词

在这个文件中，我们将学习关于 `∀` 量词。

假设 `P` 是类型 `X` 上的一个谓词。这意味着对于每一个具有类型 `X` 的数学对象 `x`，我们得到一个数学陈述 `P x`。在 Lean 中，`P x` 的类型是 `Prop`。

Lean 将 `∀ x, P x` 的证明 `h` 视为一个函数，该函数将任何 `x : X` 发送到 `P x` 的证明 `h x`。这已经解释了使用以 `∀` 开头的假设或引理的主要方法。

为了证明 `∀ x, P x`，我们使用 `intro x` 来固定一个具有类型 `X` 的任意对象，并称之为 `x` (`intro` 表示 "引入")。

同样需要注意的是，只要 `P` 的类型对 Lean 明确，我们就不需要在表达式 `∀ x, P x` 中给出 `x` 的类型，Lean 可以推断 `x` 的类型。

让我们定义一个谓词来试验 `∀`。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x
```

在下一个证明中，我们也将借此机会介绍
`unfold` 策略，这个策略简单地展开定义。在这里，这纯粹是
出于教学原因，Lean 并不需要那些 `unfold` 的调用。
我们还将使用 `rfl` 策略，该策略证明的等式是根据定义就是真的
（在非常强的意义上），它代表 "自反性"。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- Our assumption on that f is even means ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- and the same for g
  unfold even_fun at hg
  -- We need to prove ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- Let x be any real number
  intro x
  -- and let's compute
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl
}
```

像 `unfold`、`apply`、`exact`、`rfl` 和 `calc` 这样的策略将会自动展开定义。
你可以通过在上面的例子中删除 `unfold` 行来测试这个。

像 `rw`、`ring` 和 `linarith` 这样的策略通常不会展开出现在目标中的定义。
这就是为什么第一行的计算是必要的，尽管其证明就是 `rfl`。
在那行之前，`rw hf x` 不会找到任何像 `f (-x)` 这样的东西，因此会放弃。
然而，最后一行并不是必要的，因为它只证明了一个根据定义就是真的事情，并且并未跟随 `rw`。

此外，Lean 并不需要被告知在重写之前应将 `hf` 特化为 `x`，就像在第一个文件中一样。

请记住，`rw` 可以使用表达式列表进行重写。例如 `rw [h₁, h₂, h₃]` 等同于三行 `rw [h₁]`，`rw [h₂]` 和 `rw [h₃]`。注意当阅读使用此语法的证明时，你可以在重写之间检查策略状态。你只需将光标移动到列表内部即可。

因此，我们可以将上面的证明压缩为：

```lean
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}
```

现在让我们开始练习。记住，如果你需要学习如何输入一个 unicode 符号，你可以将鼠标光标放在符号上方并等待一秒钟。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  -- sorry
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x))   := by rfl
               _ = g (f x)      := by rw [hf]
  -- sorry
}
```

让我们引入更多的量词，玩玩前向和后向推理。

在接下来的定义中，注意看 `∀ x₁, ∀ x₂, ...` 是如何缩写为 `∀ x₁ x₂, ...` 的。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂
```

我们首先明确地使用正向推理。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- Since f is non-decreasing, f x₁ ≤ f x₂.
  have step₁ : f x₁ ≤ f x₂
  · exact hf x₁ x₂ h
  -- Since g is non-decreasing, we then get g (f x₁) ≤ g (f x₂).
  exact hg (f x₁) (f x₂) step₁
}
```

在上述证明中，注意到在 `hf x₁ x₂ h` 中指定 `x₁` 和 `x₂` 是多么不便，因为它们可以从 `hf` 的类型中推断出来。
我们本可以写成 `hf _ _ h` ，Lean 就会填补由 `_` 表示的空洞。
这同样适用于最后一行。

上述证明的一个可能的变化是使用 `specialize` 策略来替换 `hf` ，将其专门化为相关值。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf
}
```

这个 `specialize` 策略主要用于探索，或者为了在假设中准备重写。人们很常可以通过使用直接涉及原始假设的更复杂表达式，来替代其使用，如下一个变体所示：

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)
}
```

让我们来看一下在这里反向推理会是什么样子。
像往常一样，我们使用 `apply` 并享受 Lean 使用所谓的统一化为我们专门化假设。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- Let x₁ and x₂ be real numbers such that x₁ ≤ x₂
  intro x₁ x₂ h
  -- We need to prove (g ∘ f) x₁ ≤ (g ∘ f) x₂.
  -- Since g is non-decreasing, it suffices to prove f x₁ ≤ f x₂
  apply hg
  -- which follows from our assumption on f
  apply hf
  -- and on x₁ and x₂
  exact h
}

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by {
  -- sorry
  intro x₁ x₂ h
  apply hg
  exact hf x₁ x₂ h
  -- sorry
}
```

# 寻找引理

Lean的数学库含有许多有用的事实，
记住所有的名字是不可实现的。
以下练习将教你两种这样的技术。
* `simp` 将简化复杂的表达式。
* `apply?` 将从库中找到引理。

使用 `simp` 来证明以下内容。注意，`X : Set ℝ`表示 `X` 是一个包含（只有）实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
  -- sorry
  simp
  exact hx
  -- sorry
}
```

使用 `apply?` 找出每个具有紧致支撑的连续函数都有全局最小值的引理。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  -- sorry
  -- use `apply?` to find:
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f
  -- sorry
}
```

这是本文件的结尾，你已经学会了如何处理全称量词。
你学到了以下策略：
* `unfold`
* `specialize`
* `simp`
* `apply?`

现在，你可以选择下一步要做什么。有一个更基础的文件 `04Exists` 关于存在量词和并集。你可以先学习这个，
或者直接跳入专项文件中。如果你在任何带有 `∃`/`∧` 的事情上遇到困难，你都应该回到 `04Exists` 。

你可以从 `Topics` 文件夹中的专项文件开始。你可以选择：
* `ClassicalPropositionalLogic`（较易，逻辑）如果你希望学习如何在 Lean 中进行经典命题逻辑。
* `IntuitionisticPropositionalLogic`（较难，逻辑）如果你想要更大的挑战并进行直观命题逻辑。
* `SequenceLimit`（较易，数学）如果你想做一些基础微积分。对于这个文件，建议你先完成 `04Exists` 。
* `GaloisAjunctions`（较难，数学）如果你想要更多的抽象概念并学习如何证明完全格子之间的伴随性。
  它以产品拓扑的构造及其通用性质为结束，尽可能少地操作开集。
