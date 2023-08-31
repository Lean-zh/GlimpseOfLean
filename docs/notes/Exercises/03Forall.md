```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Instances.Real

open Function

namespace Forall
```

# 全称量词

在这个文件中，我们将学习关于 `∀` 量词。

假设 `P` 是一个谓词，作用在一个类型 `X` 上。这意味着对于每个具有类型 `X` 的数学对象 `x`，我们得到一个数学命题 `P x`。在 Lean 中，`P x` 的类型是 `Prop`。

对于 Lean 来说，一个 `∀ x, P x` 的证明 `h` 被视为一个函数，它将任意的 `x : X` 映射为 `P x` 的证明 `h x`。
这已经解释了使用以 `∀` 开始的假设或引理的主要方法。

为了证明 `∀ x, P x`，我们使用 `intro x` 来确定一个具有类型 `X` 的任意对象，并将其称为 `x`（`intro` 代表 "引入"）。

注意我们不需要在表达式 `∀ x, P x` 中给出 `x` 的类型，只要 `P` 的类型对于 Lean 是清楚的，Lean 就可以推断出 `x` 的类型。

让我们定义一个谓词，来操作 `∀`。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x
```

在下一个证明中，我们还借此机会介绍了 `unfold` 策略，它简单地展开定义。这纯粹是为了教学的目的，Lean 不需要这些 `unfold` 操作。
我们还将使用 `rfl` 策略，它证明了在定义时就为真的等式（在非常强的意义上），它代表 "反射性"。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- 我们对 f 是偶函数的假设意味着 ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- 对 g 也一样
  unfold even_fun at hg
  -- 我们需要证明 ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- 令 x 是任意的实数
  intro x
  -- 让我们计算一下
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl
}
```


像 `unfold`、`apply`、`exact`、`rfl` 和 `calc` 这样的策略会自动展开定义。
你可以通过删除上面示例中的 `unfold` 行来测试这一点。

而像 `rw`、`ring` 和 `linarith` 这样的策略通常不会展开目标中出现的定义。
这就是为什么第一行计算是必要的，尽管它的证明只是 `rfl`。
在该行之前，`rw hf x` 找不到类似于 `f (-x)` 的东西，因此会放弃。
然而，最后一行是不必要的，因为它只证明了一个在定义上为真的命题，并且后面没有跟随着 `rw`。

此外，Lean 不需要告诉它在重写之前，`hf` 应该特化为 `x`，就像在第一个文件中一样。

还要记住，`rw` 可以接受一个表达式列表来进行重写。例如 `rw [h₁, h₂, h₃]` 等同于三行 `rw [h₁]`、`rw [h₂]` 和 `rw [h₃]`。请注意，在使用此语法阅读证明时，您可以在这些重写之间检查策略状态。只需将光标移动到列表中即可。

因此，我们可以将上面的证明简化为：

```lean
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}
```

现在让我们练习一下。请记住，如果你需要学习如何输入一个 Unicode 符号，你可以将鼠标光标放在符号上并等待一秒钟。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  sorry
}
```

我们来增加更多的量词，并且玩一下正向和逆向推理。

在下面的定义中，注意 `∀ x₁, ∀ x₂, ...` 的缩写形式是 `∀ x₁ x₂, ...`。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂
```

让我们非常清晰地首先使用正向推理。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- 令 x₁ 和 x₂ 为实数，满足 x₁ ≤ x₂
  intro x₁ x₂ h
  -- 由于 f 是非递减的，所以 f x₁ ≤ f x₂。
  have step₁ : f x₁ ≤ f x₂
  · exact hf x₁ x₂ h
  -- 由于 g 是非递减的，我们得到 g (f x₁) ≤ g (f x₂)。
  exact hg (f x₁) (f x₂) step₁
}
```
在上面的证明中，注意指定 `hf x₁ x₂ h` 中的 `x₁` 和 `x₂` 是多么的不方便，因为它们可以从 `hf` 的类型中推断出来。
我们可以写成 `hf _ _ h`，而 Lean 会填充下划线所表示的空缺部分。
最后一行也适用相同的备注。

上面证明的一个可能的变化是使用 `specialize` 策略将 `hf` 替换为其对相关值的特化。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf
}
```

这个 `specialize` 策略在探索过程中或在准备重写假设时非常有用。我们往往可以通过直接涉及原始假设的更复杂的表达式来替代它的使用，就像下面的变体一样：

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)
}
```

让我们看看反向推理在这里的样子。像往常一样，在这种风格中，我们使用 `apply`，并享受 Lean 使用所谓的统一性为我们特化假设。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- 令 x₁ 和 x₂ 为实数，满足 x₁ ≤ x₂
  intro x₁ x₂ h
  -- 我们需要证明 (g ∘ f) x₁ ≤ (g ∘ f) x₂。
  -- 由于 g 是非递减的，我们只需要证明 f x₁ ≤ f x₂
  apply hg
  -- 这可以从我们对 f 的假设中得到
  apply hf
  -- 以及 x₁ 和 x₂
  exact h
}

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by {
  sorry
}
```

# 寻找引理

Lean 的数学库包含许多有用的定理，但要记住所有这些定理的名称是不可行的。
下面的练习教你两种技巧。
* `simp` 可以简化复杂的表达式。
* `apply?` 可以从库中寻找引理。

使用 `simp` 证明以下内容。注意 `X : Set ℝ`
这意味着 `X` 是一个只包含实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
  sorry
}
```

使用 `apply?` 来找到连续函数且有紧支集的函数具有全局最小值的引理。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  sorry
}
```

这是关于处理全称量词的文件的结尾。在这个文件中，你学习了以下策略：
* `unfold`
* `specialize`
* `simp`
* `apply?`

现在你可以选择下一步做什么。还有一个基本文件 `04Exists`，讲解关于存在量词和合取范畴。你现在可以开始处理它，或者直接深入到专业化的文件中。
如果你在使用 `∃`/`∧` 遇到问题，可以回来看 `04Exists`。

你可以从 `Topics` 文件夹中的专业化文件开始。你可以在以下几个选择之间进行：
* `ClassicalPropositionalLogic`（较简单，逻辑）如果你想学习如何在 Lean 中进行经典命题逻辑。
* `IntuitionisticPropositionalLogic`（较难，逻辑）如果你想要更大的挑战并进行直觉命题逻辑。
* `SequenceLimit`（较简单，数学）如果你想做一些基础微积分。对于这个文件，建议你先完成 `04Exists`。
* `GaloisAjunctions`（较难，数学）如果你想要更多的抽象，并学习如何证明完备格之间的伴随关系。它以乘积拓扑和其本征特性的构造结束，尽可能少地操作开集。
