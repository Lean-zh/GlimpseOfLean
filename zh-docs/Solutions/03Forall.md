```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Instances.Real

open Function

namespace Forall
```

# 通用量词

在此文档中，我们将了解 `∀` 量词。

设 `P` 为类型 `X` 上的谓词。这意味着对于每个具有类型 `X` 的数学对象 `x`，我们得到一个数学陈述 `P x`。在 Lean 中，`P x` 的类型是 `Prop`。

对于 `∀ x, P x` 的证明，Lean 将其视为一个函数，将任意的 `x : X` 映射到 `P x` 的证明 `h x`。
这已经解释了使用以 `∀` 开头的假设或引理的主要方式。

为了证明 `∀ x, P x`，我们使用 `intro x` 来固定一个类型为 `X` 的任意对象，并将其称为 `x`(`intro` 代表 "引入")。

还需要注意的是，在表达式 `∀ x, P x` 中，我们不需要给出 `x` 的类型，只要 `P` 的类型对于 Lean 是清晰的，Lean 就可以推断出 `x` 的类型。

让我们定义一个与 `∀` 一起使用的谓词。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x
```

在下一个证明中，我们还将利用简化 `unfold` 策略，该策略只是展开定义。这仅仅是为了教学目的，Lean 不需要这些 `unfold` 操作。我们还将使用 `rfl` 策略，该策略证明定义上成立的等式（以一种非常强的方式），它代表 "反射性"。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by {
  -- 对于 f 是偶函数的假设意味着对于每个 x，f (-x) = f x
  unfold even_fun at hf
  -- 对于 g 也是一样
  unfold even_fun at hg
  -- 我们需要证明 ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- 令 x 是任意实数
  intro x
  -- 让我们计算
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl
}
```

像 `unfold`、`apply`、`exact`、`rfl` 和 `calc` 这样的策略将自动展开定义。
您可以通过删除上面示例中的 `unfold` 行来测试这一点。

像 `rw`、`ring` 和 `linarith` 这样的策略通常不会展开目标中出现的定义。
这就是为什么第一行计算是必要的，尽管它的证明只是 `rfl`。
在这行之前，`rw hf x` 找不到类似 `f (-x)` 的东西，因此会放弃。
然而，最后一行是不必要的，因为它只证明了一个在定义上成立的事实，并且不后跟 `rw`。

此外，Lean 不需要告知在重写之前应将 `hf` 特化为 `x`，就像在第一个文件中一样。

还要记住，`rw` 可以接受一个表达式列表用于重写。例如 `rw [h₁, h₂, h₃]` 等价于三行 `rw [h₁]`、`rw [h₂]` 和 `rw [h₃]`。请注意，在使用此语法读取证明时，您可以在这些重写之间检查策略状态。您只需要将光标移动到列表内部即可。

因此，我们可以将上面的证明压缩为：

```lean
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by {
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]
}
```

现在我们来练习一下。请记住，如果您需要学习如何输入一个 Unicode 符号，您可以将鼠标光标放在该符号上等待一秒钟。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by {
  -- 抱歉
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x))   := by rfl
               _ = g (f x)      := by rw [hf]
  -- 抱歉
}
```

让我们来谈谈更多的量词，并进行正向和逆向推理。

在下面的定义中，注意 `∀ x₁, ∀ x₂, ...` 是缩写为 `∀ x₁ x₂, ...`。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂
```

让我们非常明确地使用正向推理。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- 令 x₁ 和 x₂ 是实数，满足 x₁ ≤ x₂
  intro x₁ x₂ h
  -- 由于 f 是非递减的，因此 f x₁ ≤ f x₂。
  have step₁ : f x₁ ≤ f x₂
  · exact hf x₁ x₂ h
  -- 由于 g 是非递减的，我们得到 g (f x₁) ≤ g (f x₂)。
  exact hg (f x₁) (f x₂) step₁
}
```

在上面的证明中，请注意在 `hf x₁ x₂ h` 中指定 `x₁` 和 `x₂` 是多么的不便，因为它们可以从 `hf` 的类型中推断出来。
我们可以写成 `hf _ _ h`，Lean 会自动填充 `_` 所表示的空位。
同样的备注也适用于最后一行。

上面证明的一个可能变体是使用 `specialize` 策略，将 `hf` 替换为其与相关值的特化。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf
}
```

`specialize` 策略在探索或准备重写假设时非常有用。在很多情况下，我们可以将其用更复杂的表达式直接涉及原始假设来代替 `specialize` 的使用，就像下面的变体一样：

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)
}
```

让我们看看逆向推理在这里是怎么样的。
像往常一样，在这种风格中，我们使用 `apply` 并利用 Lean 使用所谓的统一化为我们特定的假设。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by {
  -- 令 x₁ 和 x₂ 是实数，满足 x₁ ≤ x₂
  intro x₁ x₂ h
  -- 我们需要证明 (g ∘ f) x₁ ≤ (g ∘ f) x₂。
  -- 由于 g 是非递减的，我们只需要证明 f x₁ ≤ f x₂
  apply hg
  -- 这可以根据我们对 f 的假设得出
  apply hf
  -- 以及对 x₁ 和 x₂ 的假设
  exact h
}

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by {
  -- 抱歉
  intro x₁ x₂ h
  apply hg
  exact hf x₁ x₂ h
  -- 抱歉
}
```

# 查找引理

Lean的数学库包含许多有用的定理，记住它们所有的名字几乎是不可行的。
以下练习将教您两种查找引理的技巧。
* `simp` 可以简化复杂的表达式。
* `apply?` 可以从库中查找引理。

使用 `simp` 来证明以下命题。注意 `X : Set ℝ` 表示 `X` 是一个包含（仅）实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by {
  -- 抱歉
  simp
  exact hx
  -- 抱歉
}
```

使用 `apply?` 来找到具有紧致支持的连续函数具有全局最小值的引理。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by {
  -- 抱歉
  -- 使用 `apply?` 来查找：
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f
  -- 抱歉
}
```

至此，您已经完成了关于处理全称量词的文件。
您已经了解了一些策略:
* `unfold`
* `specialize`
* `simp`
* `apply?`

您现在可以选择下一步要做什么。还有一个基本的文件 `04Exists`，关于存在量词和合取。
您可以现在处理它，或者直接进入其中一个专门的文件。
如果您在处理 `∃`/`∧` 方面遇到困难，可以回到 `04Exists`。

您可以从 `Topics` 文件夹中的专门文件开始。您可以选择以下文件之一：
* `ClassicalPropositionalLogic`（更容易，逻辑）如果您希望学习如何在 Lean 中进行经典命题逻辑。
* `IntuitionisticPropositionalLogic`（更难，逻辑）如果您想挑战更大，并进行直觉式命题逻辑。
* `SequenceLimit`（更容易，数学）如果您想进行一些基本的微积分。
  对于此文件，建议先处理 `04Exists`。
* `GaloisAjunctions`（更难，数学）如果您想进行更多的抽象，并学习如何证明完全格之间的伴随性质。
  它以乘积拓扑的构造及其泛性质结束，尽可能少地操作开集。
