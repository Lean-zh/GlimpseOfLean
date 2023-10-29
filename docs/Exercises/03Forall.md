```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Instances.Real

open Function

namespace Forall
```

# 通用量词

在这个文件中，我们将了解`∀`量词。

设`P`是一种类型`X`的谓词。这意味着对于每一个类型为`X`的数学对象`x`，我们得到一个数学语句`P x`。
在 Lean 中，`P x`的类型为`Prop`。

Lean 将证明`h`为`∀ x, P x`视为一个函数，将任意的`x : X`送入证明`h x`中，证实`P x`。
这已经解释了使用假设或引理的主要方法，该假设或引理开始于`∀`。

为了证明`∀ x, P x`，我们使用`intro x`来固定一个具有类型`X`的任意对象，并称之为`x`（`intro`代表 "介绍"）。

同时请注意，只要 Lean 能明白`P`的类型，我们在表达式`∀ x, P x`中不需要给出`x`的类型，因为它可以推断出`x`的类型。

让我们定义一个谓词来试验`∀`。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x
```

在下一个证明中，我们也利用机会介绍 `unfold` 策略，它只是展开定义。这里完全出于教学原因，Lean 并不需要那些 `unfold` 的调用。
我们还将使用 `rfl` 策略，它证明了根据定义就为真的等式（在很强的意义上），代表 "反射性"。

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

像 `unfold`，`apply`，`exact`，`rfl` 和 `calc` 这样的策略将会自动展开定义。
你可以通过在上述示例中删除 `unfold` 行来测试它。

像 `rw`，`ring` 和 `linarith` 这样的策略通常不会展开目标中出现的定义。
这就是为什么必须要有第一行计算行，尽管它的证明就是 `rfl`。
在那行之前，`rw hf x` 找不到任何类似 `f (-x)` 的东西，因此会放弃。
但最后一行并不必要，因为它只证明了一个根据定义就是真实的事情，并且没有后面的 `rw`。

此外，Lean 不需要被告知在重写之前应该将 `hf` 专用于 `x`，就像在第一个文件中一样。

还要记住，`rw` 可以采用一个表达式列表来用于重写。例如 `rw [h₁, h₂, h₃]` 等效于三行 `rw [h₁]`，`rw [h₂]` 和 `rw [h₃]`。请注意，当你使用这种语法阅读一个证明时，你可以在这些重写之间查看策略状态。你只需要将光标移到列表内部就可以。

因此，我们可以将上述证明压缩为：

```lean
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}
```

现在让我们开始练习。请记住，如果你需要学习如何输入一个 unicode 符号，你可以把你的鼠标光标放在符号上面并等待一秒钟。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  sorry
}
```

让我们使用更多的量词，并且尝试使用前向和后向推理。

在下面的定义中，注意如何将`∀ x₁, ∀ x₂, ...`缩写为`∀ x₁ x₂, ...`。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂
```

让我们首先非常明确地使用前向推理。

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

在上述证明中，注意到指定 `hf x₁ x₂ h` 中的 `x₁` 和 `x₂` 是多么不方便，因为它们可以从 `hf` 的类型中推断出来。
我们本来可以写成 `hf _ _ h` ，Lean 就会自动填充由 `_` 表示的空缺。
对于最后一行，也有同样的问题。

对上述证明的一种可能的变种是
使用 `specialize` 策略来替换 `hf` 为其对相关值的特化。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf
}
```

这种 `specialize` 策略主要用于探索，或者为在假设中进行重写做准备。人们通常可以通过使用直接涉及原始假设的更复杂的表达式来替换其使用，如下一种变体：

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)
}
```

让我们来看看这里的反向推理是什么样子的。
像往常一样，我们使用 `apply` 并且享受 Lean 使用所谓的统一方法为我们专门化假设。

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
  sorry
}
```

# 查找引理

Lean 的数学库包含许多有用的事实，记住所有这些事实是不切实际的。以下练习将教你两种此类技巧。
* `simp` 将简化复杂的表达式。
* `apply?` 将从库中找到引理。

使用 `simp` 来证明以下内容。注意 `X : Set ℝ`
表示 `X` 是一个只包含实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
  sorry
}
```

使用 `apply?` 来找出这个引理，即每个具有紧致支持的连续函数都具有全局最小值。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  sorry
}
```

这是这个文件的结束，你学习了如何处理通用量词。
你学习了以下策略：
* `unfold`
* `specialize`
* `simp`
* `apply?`

你现在可以选择下一步要做什么。还有一个基本文件 `04Exists`
关于存在量词和连接词。你可以现在就处理，
或者直接深入专业文件中。
在后者的情况下，如果你在 `∃`/`∧` 遇到任何问题，你应该回到 `04Exists` 。

你可以从 `Topics` 文件夹中的专业文件开始。你可以选择
* `ClassicalPropositionalLogic`（更简单，逻辑） 如果你想学习
  如何在 Lean 中进行经典命题逻辑。
* `IntuitionisticPropositionalLogic`（更难，逻辑） 如果你想挑战更大
  并进行直觉主义命题逻辑。
* `SequenceLimit` （更简单，数学） 如果你想做一些初级微积分。
  对于这个文件，建议先处理 `04Exists` 。
* `GaloisAjunctions`（更难，数学） 如果你想有更多的抽象化
  并学习如何证明完全格之间的伴随性的事情。
  它以产品拓扑的构造及其普遍属性结束
  尽可能少地操作开放集。
